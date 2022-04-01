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
    messages: Vec<Any>,
    account_sequence: AccountSequence,
    account_number: AccountNumber,
    key_entry: &KeyEntry,
    tx_memo: &Memo,
) -> Result<Response, Error> {
    let fee = estimate_tx_fees(
        config,
        grpc_address,
        account_sequence,
        account_number,
        messages.clone(),
        key_entry,
        tx_memo,
    )
    .await?;

    raw_send_tx(
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

pub async fn raw_send_tx(
    config: &ChainConfig,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    fee: &Fee,
    account_sequence: AccountSequence,
    account_number: AccountNumber,
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
