use ibc_proto::{
    cosmos::tx::v1beta1::Fee,
    google::protobuf::Any,
};
use ibc_relayer_types::events::IbcEvent;
use tendermint_rpc::{
    endpoint::broadcast::tx_sync::Response,
    Client,
    HttpClient,
    Url,
};

use super::batch::send_batched_messages_and_wait_commit;
use crate::{
    chain::cosmos::{
        encode::sign_and_encode_tx,
        estimate::estimate_tx_fees,
        query::{
            account::query_account,
            tx::all_ibc_events_from_tx_search_response,
        },
        types::{
            account::Account,
            config::TxConfig,
        },
        wait::wait_tx_succeed,
    },
    config::types::Memo,
    error::Error,
    event::IbcEventWithHeight,
    keyring::{
        Secp256k1KeyPair,
        SigningKeyPair,
    },
};

pub async fn estimate_fee_and_send_tx(
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
) -> Result<Response, Error> {
    let fee = estimate_tx_fees(config, key_pair, account, tx_memo, messages).await?;

    send_tx_with_fee(
        rpc_client, config, key_pair, account, tx_memo, messages, &fee,
    )
    .await
}

async fn send_tx_with_fee(
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
    fee: &Fee,
) -> Result<Response, Error> {
    let tx_bytes = sign_and_encode_tx(config, key_pair, account, tx_memo, messages, fee)?;

    let response = broadcast_tx_sync(rpc_client, &config.rpc_address, tx_bytes).await?;

    Ok(response)
}

/// Perform a `broadcast_tx_sync`, and return the corresponding deserialized response data.
pub async fn broadcast_tx_sync(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    data: Vec<u8>,
) -> Result<Response, Error> {
    let response = rpc_client
        .broadcast_tx_sync(data)
        .await
        .map_err(|e| Error::rpc(rpc_address.clone(), e))?;

    Ok(response)
}

/**
 A simplified version of send_tx that does not depend on `ChainHandle`.

 This allows different wallet ([`Secp256k1KeyPair`]) to be used for
 submitting transactions. The simple behavior as follows:

 - Query the account information on the fly. This may introduce more
   overhead in production, but does not matter in testing.
 - Do not split the provided messages into smaller batches.
 - Wait for TX sync result, and error if any result contains
   error event.
*/
pub async fn simple_send_tx(
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    messages: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let key_account = key_pair.account();
    let account = query_account(&config.grpc_address, &key_account)
        .await?
        .into();

    let response = estimate_fee_and_send_tx(
        rpc_client,
        config,
        key_pair,
        &account,
        &Memo::default(),
        &messages,
    )
    .await?;

    if response.code.is_err() {
        return Err(Error::check_tx(response));
    }

    let response = wait_tx_succeed(
        rpc_client,
        &config.rpc_address,
        &config.rpc_timeout,
        &response.hash,
    )
    .await?;

    let events = all_ibc_events_from_tx_search_response(&config.chain_id, response);

    Ok(events)
}

pub async fn batched_send_tx(
    rpc_client: &HttpClient,
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    messages: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let key_account = key_pair.account();
    let mut account = query_account(&config.grpc_address, &key_account)
        .await?
        .into();

    let events = send_batched_messages_and_wait_commit(
        rpc_client,
        config,
        key_pair,
        &mut account,
        &Memo::default(),
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
