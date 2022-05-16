use core::str::FromStr;
use core::time::Duration;
use eyre::eyre;
use http::uri::Uri;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;
use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::gas::calculate_fee;
use ibc_relayer::chain::cosmos::query::account::query_account;
use ibc_relayer::chain::cosmos::tx::estimate_fee_and_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::cosmos::types::gas::GasConfig;
use ibc_relayer::chain::cosmos::types::tx::TxSyncResult;
use ibc_relayer::chain::cosmos::wait::wait_for_block_commits;
use ibc_relayer::config::GasPrice;
use ibc_relayer::keyring::KeyEntry;
use tendermint_rpc::{HttpClient, Url};

use crate::error::{handle_generic_error, Error};

pub fn gas_config_for_test() -> GasConfig {
    let max_gas = 3000000;
    let gas_adjustment = 0.1;
    let gas_price = GasPrice::new(0.001, "stake".to_string());

    let default_gas = max_gas;
    let fee_granter = "".to_string();

    let max_fee = Fee {
        amount: vec![calculate_fee(max_gas, &gas_price)],
        gas_limit: max_gas,
        payer: "".to_string(),
        granter: fee_granter.clone(),
    };

    GasConfig {
        default_gas,
        max_gas,
        gas_adjustment,
        gas_price,
        max_fee,
        fee_granter,
    }
}

pub fn new_tx_config_for_test(
    chain_id: ChainId,
    raw_rpc_address: String,
    raw_grpc_address: String,
) -> Result<TxConfig, Error> {
    let rpc_address = Url::from_str(&raw_rpc_address).map_err(handle_generic_error)?;

    let rpc_client = HttpClient::new(rpc_address.clone()).map_err(handle_generic_error)?;

    let grpc_address = Uri::from_str(&raw_grpc_address).map_err(handle_generic_error)?;

    let gas_config = gas_config_for_test();

    let rpc_timeout = Duration::from_secs(30);

    let address_type = Default::default();

    Ok(TxConfig {
        chain_id,
        gas_config,
        rpc_client,
        rpc_address,
        grpc_address,
        rpc_timeout,
        address_type,
    })
}

/**
 A simplified version of send_tx that does not depend on `ChainHandle`.

 This allows different wallet ([`KeyEntry`]) to be used for submitting
 transactions. The simple behavior as follows:

 - Query the account information on the fly. This may introduce more
   overhead in production, but does not matter in testing.
 - Do not split the provided messages into smaller batches.
 - Wait for TX sync result, and error if any result contains
   error event.
*/
pub async fn simple_send_tx(
    config: &TxConfig,
    key_entry: &KeyEntry,
    messages: Vec<Any>,
) -> Result<(), Error> {
    let account = query_account(&config.grpc_address, &key_entry.account)
        .await?
        .into();

    let message_count = messages.len();

    let response =
        estimate_fee_and_send_tx(config, key_entry, &account, &Default::default(), messages)
            .await?;

    let events_per_tx = vec![IbcEvent::default(); message_count];

    let tx_sync_result = TxSyncResult {
        response,
        events: events_per_tx,
    };

    let mut tx_sync_results = vec![tx_sync_result];

    wait_for_block_commits(
        &config.chain_id,
        &config.rpc_client,
        &config.rpc_address,
        &config.rpc_timeout,
        &mut tx_sync_results,
    )
    .await?;

    for result in tx_sync_results.iter() {
        for event in result.events.iter() {
            if let IbcEvent::ChainError(e) = event {
                return Err(Error::generic(eyre!("send_tx result in error: {}", e)));
            }
        }
    }

    Ok(())
}
