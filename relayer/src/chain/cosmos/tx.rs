use ibc_proto::cosmos::tx::v1beta1::Fee;
use ibc_proto::google::protobuf::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;
use tendermint_rpc::{Client, HttpClient, Url};

use crate::chain::cosmos::encode::sign_and_encode_tx;
use crate::chain::cosmos::estimate::estimate_tx_fees;
use crate::chain::cosmos::types::account::Account;
use crate::chain::cosmos::types::config::TxConfig;
use crate::config::types::Memo;
use crate::error::Error;
use crate::keyring::KeyEntry;

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
