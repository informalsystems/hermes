use ibc_proto::cosmos::tx::v1beta1::Fee;
use prost_types::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{HttpClient, Url};
use tonic::codegen::http::Uri;
use tracing::{debug, error};

use crate::chain::cosmos::batch::batch_messages;
use crate::chain::cosmos::broadcast_tx_sync;
use crate::chain::cosmos::encode::sign_and_encode_tx;
use crate::chain::cosmos::estimate::estimate_tx_fees;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;
use crate::sdk_error::sdk_error_from_tx_sync_error_code;

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
