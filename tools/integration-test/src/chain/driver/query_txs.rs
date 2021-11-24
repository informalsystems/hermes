/*!
   Methods for querying transactions on a chain.
*/

use serde_json as json;

use crate::error::Error;
use crate::types::wallet::WalletAddress;

use super::ChainDriver;

/**
    Query for the transactions related to a wallet on `Chain`
    receiving token transfer from others.
*/
pub fn query_recipient_transactions(
    driver: &ChainDriver,
    recipient_address: &WalletAddress,
) -> Result<json::Value, Error> {
    let res = driver.exec(&[
        "--node",
        &driver.rpc_listen_address(),
        "query",
        "txs",
        "--events",
        &format!("transfer.recipient={}", recipient_address),
    ])?;

    // tracing::debug!("parsing tx result: {}", res);

    let json_res = json::from_str(&res)?;

    Ok(json_res)
}
