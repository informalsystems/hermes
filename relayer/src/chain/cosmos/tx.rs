use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{Client, HttpClient, Url};
use tonic::codegen::http::Uri;

use crate::chain::cosmos::account::{AccountNumber, AccountSequence};
use crate::chain::cosmos::encode::sign_and_encode_tx;
use crate::chain::cosmos::estimate::estimate_tx_fees;
use crate::config::types::Memo;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::KeyEntry;

pub async fn estimate_fee_and_send_tx(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    grpc_address: &Uri,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
    account_number: AccountNumber,
    account_sequence: AccountSequence,
    messages: Vec<Any>,
) -> Result<Response, Error> {
    let fee = estimate_tx_fees(
        config,
        grpc_address,
        key_entry,
        tx_memo,
        account_number,
        account_sequence,
        messages.clone(),
    )
    .await?;

    send_tx_with_fee(
        config,
        rpc_client,
        rpc_address,
        key_entry,
        tx_memo,
        account_number,
        account_sequence,
        messages,
        &fee,
    )
    .await
}

pub async fn send_tx_with_fee(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
    account_number: AccountNumber,
    account_sequence: AccountSequence,
    messages: Vec<Any>,
    fee: &Fee,
) -> Result<Response, Error> {
    let tx_bytes = sign_and_encode_tx(
        config,
        key_entry,
        tx_memo,
        account_number,
        account_sequence,
        messages,
        fee,
    )?;

    let response = broadcast_tx_sync(rpc_client, rpc_address, tx_bytes).await?;

    Ok(response)
}

/// Perform a `broadcast_tx_sync`, and return the corresponding deserialized response data.
pub async fn broadcast_tx_sync(
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
