use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::tx::v1beta1::{Fee, Tx};
use ibc_proto::google::protobuf::Any;
use tonic::codegen::http::Uri;
use tracing::{debug, error};

use crate::chain::cosmos::account::{AccountNumber, AccountSequence};
use crate::chain::cosmos::encode::encode_tx_to_raw;
use crate::chain::cosmos::gas::gas_amount_to_fees;
use crate::chain::cosmos::simulate::send_tx_simulate;
use crate::chain::cosmos::types::GasConfig;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;

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

pub async fn estimate_tx_fees(
    config: &ChainConfig,
    grpc_address: &Uri,
    account_sequence: AccountSequence,
    account_number: AccountNumber,
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
