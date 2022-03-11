use core::cmp::min;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{
    Fee, ModeInfo, SignDoc, SignerInfo, SimulateRequest, SimulateResponse, Tx, TxRaw,
};
use prost_types::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{HttpClient, Url};
use tonic::codegen::http::Uri;
use tracing::{debug, error};

use crate::chain::cosmos::types::{GasConfig, SignedTx};
use crate::chain::cosmos::{
    auth_info_and_bytes, broadcast_tx_sync, calculate_fee, mul_ceil, tx_body_and_bytes,
};
use crate::config::types::Memo;
use crate::config::AddressType;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::{sign_message, KeyEntry};
use crate::sdk_error::sdk_error_from_tx_sync_error_code;

pub fn encode_key_bytes(key: &KeyEntry) -> Result<Vec<u8>, Error> {
    let mut pk_buf = Vec::new();

    prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf)
        .map_err(|e| Error::protobuf_encode("PublicKey".into(), e))?;

    Ok(pk_buf)
}

pub fn encode_sign_doc(
    chain_id: &ChainId,
    key: &KeyEntry,
    address_type: &AddressType,
    body_bytes: Vec<u8>,
    auth_info_bytes: Vec<u8>,
    account_number: u64,
) -> Result<Vec<u8>, Error> {
    let sign_doc = SignDoc {
        body_bytes,
        auth_info_bytes,
        chain_id: chain_id.to_string(),
        account_number,
    };

    // A protobuf serialization of a SignDoc
    let mut signdoc_buf = Vec::new();
    prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

    let signed = sign_message(key, signdoc_buf, address_type).map_err(Error::key_base)?;

    Ok(signed)
}

pub fn encode_signer_info(
    key_bytes: Vec<u8>,
    address_type: &AddressType,
    sequence: u64,
) -> Result<SignerInfo, Error> {
    let pk_type = match address_type {
        AddressType::Cosmos => "/cosmos.crypto.secp256k1.PubKey".to_string(),
        AddressType::Ethermint { pk_type } => pk_type.clone(),
    };
    // Create a MsgSend proto Any message
    let pk_any = Any {
        type_url: pk_type,
        value: key_bytes,
    };

    let single = Single { mode: 1 };
    let sum_single = Some(Sum::Single(single));
    let mode = Some(ModeInfo { sum: sum_single });
    let signer_info = SignerInfo {
        public_key: Some(pk_any),
        mode_info: mode,
        sequence,
    };
    Ok(signer_info)
}

pub fn batch_messages(
    messages: Vec<Any>,
    max_message_count: usize,
    max_tx_size: usize,
) -> Result<Vec<Vec<Any>>, Error> {
    let mut batches = vec![];

    let mut current_count = 0;
    let mut current_size = 0;
    let mut current_batch = vec![];

    for message in messages.into_iter() {
        current_count += 1;
        current_size += message_size(&message)?;
        current_batch.push(message);

        if current_count >= max_message_count || current_size >= max_tx_size {
            let insert_batch = current_batch.drain(..).collect();
            batches.push(insert_batch);
            current_count = 0;
            current_size = 0;
        }
    }

    if !current_batch.is_empty() {
        batches.push(current_batch);
    }

    Ok(batches)
}

pub fn message_size(message: &Any) -> Result<usize, Error> {
    let mut buf = Vec::new();

    prost::Message::encode(message, &mut buf)
        .map_err(|e| Error::protobuf_encode("Message".into(), e))?;

    Ok(buf.len())
}

pub async fn estimate_gas(
    chain_id: &ChainId,
    tx: Tx,
    grpc_address: &Uri,
    default_gas: u64,
    max_gas: u64,
) -> Result<u64, Error> {
    let response = send_tx_simulate(tx, grpc_address).await;

    let estimated_gas = match response {
        Ok(response) => {
            let m_gas_info = response.gas_info;

            debug!(
                "[{}] send_tx: tx simulation successful, simulated gas: {:?}",
                chain_id, m_gas_info,
            );

            match m_gas_info {
                Some(gas) => gas.gas_used,
                None => default_gas,
            }
        }
        Err(e) => {
            error!(
                "[{}] send_tx: failed to estimate gas, falling back on default gas, error: {}",
                chain_id,
                e.detail()
            );

            default_gas
        }
    };

    if estimated_gas > max_gas {
        debug!(
            estimated = ?estimated_gas,
            max = ?max_gas,
            "[{}] send_tx: estimated gas is higher than max gas",
            chain_id,
        );

        Err(Error::tx_simulate_gas_estimate_exceeded(
            chain_id.clone(),
            estimated_gas,
            max_gas,
        ))
    } else {
        Ok(estimated_gas)
    }
}

pub async fn send_messages_as_batches(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    grpc_address: &Uri,
    messages: Vec<Any>,
    account_sequence: &mut u64,
    account_number: u64,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Vec<Response>, Error> {
    let max_message_count = config.max_msg_num.0;
    let max_tx_size = config.max_tx_size.into();

    if messages.is_empty() {
        return Ok(Vec::new());
    }

    let batches = batch_messages(messages, max_message_count, max_tx_size)?;

    let mut responses = Vec::new();

    for batch in batches {
        let response = estimate_fee_and_send_tx(
            config,
            rpc_client,
            rpc_address,
            grpc_address,
            batch,
            account_sequence,
            account_number,
            key_entry,
            tx_memo,
        )
        .await?;

        responses.push(response);
    }

    Ok(responses)
}

pub async fn estimate_fee_and_send_tx(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    grpc_address: &Uri,
    messages: Vec<Any>,
    account_sequence: &mut u64,
    account_number: u64,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Response, Error> {
    let fee = estimate_tx_fees(
        config,
        grpc_address,
        *account_sequence,
        account_number,
        messages.clone(),
        key_entry,
        tx_memo,
    )
    .await?;

    send_tx_and_update_account_sequence(
        config,
        rpc_client,
        rpc_address,
        &fee,
        account_sequence,
        account_number,
        messages,
        key_entry,
        tx_memo,
    )
    .await
}

pub async fn send_tx_and_update_account_sequence(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    fee: &Fee,
    account_sequence: &mut u64,
    account_number: u64,
    messages: Vec<Any>,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Response, Error> {
    let response = raw_send_tx(
        config,
        rpc_client,
        rpc_address,
        fee,
        *account_sequence,
        account_number,
        messages,
        key_entry,
        tx_memo,
    )
    .await?;

    match response.code {
        tendermint::abci::Code::Ok => {
            // A success means the account s.n. was increased
            *account_sequence += 1;
            debug!("[{}] send_tx: broadcast_tx_sync: {:?}", config.id, response);
        }
        tendermint::abci::Code::Err(code) => {
            // Avoid increasing the account s.n. if CheckTx failed
            // Log the error
            error!(
                "[{}] send_tx: broadcast_tx_sync: {:?}: diagnostic: {:?}",
                config.id,
                response,
                sdk_error_from_tx_sync_error_code(code)
            );
        }
    }

    Ok(response)
}

pub async fn raw_send_tx(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    fee: &Fee,
    account_sequence: u64,
    account_number: u64,
    messages: Vec<Any>,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Response, Error> {
    let tx_bytes = sign_and_encode_tx(
        config,
        messages,
        account_sequence,
        key_entry,
        fee,
        tx_memo,
        account_number,
    )?;

    let response = broadcast_tx_sync(rpc_client, rpc_address, tx_bytes).await?;

    Ok(response)
}

pub async fn estimate_tx_fees(
    config: &ChainConfig,
    grpc_address: &Uri,
    account_sequence: u64,
    account_number: u64,
    messages: Vec<Any>,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Fee, Error> {
    let gas_config = GasConfig::from_chain_config(config);

    let signed_tx = encode_tx_to_raw(
        config,
        messages,
        account_sequence,
        key_entry,
        &gas_config.max_fee,
        tx_memo,
        account_number,
    )?;

    let tx = Tx {
        body: Some(signed_tx.body),
        auth_info: Some(signed_tx.auth_info),
        signatures: signed_tx.signatures,
    };

    let estimated_fee = estimate_gas_with_raw_tx(&gas_config, &config.id, grpc_address, tx).await?;

    Ok(estimated_fee)
}

pub fn sign_and_encode_tx(
    config: &ChainConfig,
    messages: Vec<Any>,
    account_sequence: u64,
    key_entry: &KeyEntry,
    fee: &Fee,
    tx_memo: &Memo,
    account_number: u64,
) -> Result<Vec<u8>, Error> {
    let signed_tx = encode_tx_to_raw(
        config,
        messages,
        account_sequence,
        key_entry,
        fee,
        tx_memo,
        account_number,
    )?;

    let tx_raw = TxRaw {
        body_bytes: signed_tx.body_bytes,
        auth_info_bytes: signed_tx.auth_info_bytes,
        signatures: signed_tx.signatures,
    };

    encode_tx_raw(tx_raw)
}

pub fn encode_tx_raw(tx_raw: TxRaw) -> Result<Vec<u8>, Error> {
    let mut tx_bytes = Vec::new();
    prost::Message::encode(&tx_raw, &mut tx_bytes)
        .map_err(|e| Error::protobuf_encode("Transaction".to_string(), e))?;

    Ok(tx_bytes)
}

pub fn encode_tx_to_raw(
    config: &ChainConfig,
    messages: Vec<Any>,
    account_sequence: u64,
    key_entry: &KeyEntry,
    fee: &Fee,
    tx_memo: &Memo,
    account_number: u64,
) -> Result<SignedTx, Error> {
    let key_bytes = encode_key_bytes(key_entry)?;

    let signer = encode_signer_info(key_bytes, &config.address_type, account_sequence)?;

    let (body, body_bytes) = tx_body_and_bytes(messages, tx_memo)?;

    let (auth_info, auth_info_bytes) = auth_info_and_bytes(signer, fee.clone())?;

    let signed_doc = encode_sign_doc(
        &config.id,
        key_entry,
        &config.address_type,
        body_bytes.clone(),
        auth_info_bytes.clone(),
        account_number,
    )?;

    Ok(SignedTx {
        body,
        body_bytes,
        auth_info,
        auth_info_bytes,
        signatures: vec![signed_doc],
    })
}

pub async fn send_tx_simulate(tx: Tx, grpc_address: &Uri) -> Result<SimulateResponse, Error> {
    use ibc_proto::cosmos::tx::v1beta1::service_client::ServiceClient;

    // The `tx` field of `SimulateRequest` was deprecated in Cosmos SDK 0.43 in favor of `tx_bytes`.
    let mut tx_bytes = vec![];
    prost::Message::encode(&tx, &mut tx_bytes).unwrap(); // FIXME: Handle error here

    #[allow(deprecated)]
    let req = SimulateRequest {
        tx: Some(tx), // needed for simulation to go through with Cosmos SDK <  0.43
        tx_bytes,     // needed for simulation to go through with Cosmos SDk >= 0.43
    };

    let mut client = ServiceClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(req);
    let response = client
        .simulate(request)
        .await
        .map_err(Error::grpc_status)?
        .into_inner();

    Ok(response)
}

pub async fn estimate_gas_with_raw_tx(
    gas_config: &GasConfig,
    chain_id: &ChainId,
    grpc_address: &Uri,
    tx: Tx,
) -> Result<Fee, Error> {
    let response = send_tx_simulate(tx, grpc_address).await;

    let estimated_gas = match response {
        Ok(response) => {
            let m_gas_info = response.gas_info;

            debug!(
                "[{}] send_tx: tx simulation successful, simulated gas: {:?}",
                chain_id, m_gas_info,
            );

            match m_gas_info {
                Some(gas) => gas.gas_used,
                None => gas_config.default_gas,
            }
        }
        Err(e) => {
            error!(
                "[{}] send_tx: failed to estimate gas, falling back on default gas, error: {}",
                chain_id,
                e.detail()
            );

            gas_config.default_gas
        }
    };

    if estimated_gas > gas_config.max_gas {
        debug!(
            estimated = ?estimated_gas,
            max = ?gas_config.max_gas,
            "[{}] send_tx: estimated gas is higher than max gas",
            chain_id,
        );

        Err(Error::tx_simulate_gas_estimate_exceeded(
            chain_id.clone(),
            estimated_gas,
            gas_config.max_gas,
        ))
    } else {
        Ok(gas_amount_to_fees(gas_config, estimated_gas))
    }
}

pub fn gas_amount_to_fees(config: &GasConfig, gas_amount: u64) -> Fee {
    let gas_limit = adjust_gas_with_simulated_fees(config, gas_amount);

    let amount = calculate_fee(gas_limit, &config.gas_price);

    Fee {
        amount: vec![amount],
        gas_limit,
        payer: "".to_string(),
        granter: "".to_string(),
    }
}

/// Adjusts the fee based on the configured `gas_adjustment` to prevent out of gas errors.
/// The actual gas cost, when a transaction is executed, may be slightly higher than the
/// one returned by the simulation.
pub fn adjust_gas_with_simulated_fees(config: &GasConfig, gas_amount: u64) -> u64 {
    let gas_adjustment = config.gas_adjustment;
    let max_gas = config.max_gas;

    let (_, digits) = mul_ceil(gas_amount, gas_adjustment).to_u64_digits();
    assert!(digits.len() == 1);

    let adjustment = digits[0];
    let gas = gas_amount.checked_add(adjustment).unwrap_or(u64::MAX);

    min(gas, max_gas)
}
