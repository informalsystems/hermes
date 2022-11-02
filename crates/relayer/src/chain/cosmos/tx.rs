use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::events::IbcEvent;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{Client, HttpClient, Url};

use crate::chain::cosmos::encode::sign_and_encode_tx;
use crate::chain::cosmos::estimate::estimate_tx_fees;
use crate::chain::cosmos::query::account::query_account;
use crate::chain::cosmos::query::tx::all_ibc_events_from_tx_search_response;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::wait::wait_tx_succeed;
use crate::config::types::Memo;
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::keyring::KeyEntry;

use super::batch::send_batched_messages_and_wait_commit;

pub async fn estimate_fee_and_send_tx(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    let fee = estimate_tx_fees(config, key_entry, account, tx_memo, messages).await?;

    send_tx_with_fee(config, key_entry, account, tx_memo, messages, &fee).await
}

async fn send_tx_with_fee(
    config: &TxConfig,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
    fee: &Fee,
) -> Result<Response, Error> {
    let tx_bytes = sign_and_encode_tx(config, key_entry, account, tx_memo, messages, fee)?;

    let response = broadcast_tx_sync(&config.rpc_client, &config.rpc_address, tx_bytes).await?;

    Ok(response)
}

/// Perform a `broadcast_tx_sync`, and return the corresponding deserialized response data.
async fn broadcast_tx_sync(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    data: Vec<u8>,
) -> Result<Response, Error> {
    let response = rpc_client
        .broadcast_tx_sync(data.into())
        .await
        .map_err(|e| Error::rpc(rpc_address.clone(), e))?;

    Ok(response)
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
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let account = query_account(&config.grpc_address, &key_entry.account)
        .await?
        .into();

    let response =
        estimate_fee_and_send_tx(config, key_entry, &account, &Default::default(), &messages)
            .await?;

    if response.code.is_err() {
        return Err(Error::check_tx(response));
    }

    let response = wait_tx_succeed(
        &config.rpc_client,
        &config.rpc_address,
        &config.rpc_timeout,
        &response.hash,
    )
    .await?;

    let events = all_ibc_events_from_tx_search_response(&config.chain_id, response);

    Ok(events)
}

pub async fn batched_send_tx(
    config: &TxConfig,
    key_entry: &KeyEntry,
    messages: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let mut account = query_account(&config.grpc_address, &key_entry.account)
        .await?
        .into();

    let events = send_batched_messages_and_wait_commit(
        config,
        config.max_msg_num,
        config.max_tx_size,
        key_entry,
        &mut account,
        &Default::default(),
        messages,
    )
    .await?;

    for event in &events {
        if let IbcEvent::ChainError(ref e) = event.event {
            return Err(Error::send_tx(e.clone()));
        }
    }

    Ok(events)
}
