use ibc::core::ics24_host::identifier::ChainId;
use ibc::Height;
use tendermint_rpc::{Client, HttpClient, Url};

use crate::chain::endpoint::ChainStatus;
use crate::error::Error;

/// Query the chain status via an RPC query.
///
/// Returns an error if the node is still syncing and has not caught up,
/// ie. if `sync_info.catching_up` is `true`.
pub async fn query_status(
    chain_id: &ChainId,
    rpc_client: &HttpClient,
    rpc_address: &Url,
) -> Result<ChainStatus, Error> {
    let response = rpc_client
        .status()
        .await
        .map_err(|e| Error::rpc(rpc_address.clone(), e))?;

    if response.sync_info.catching_up {
        return Err(Error::chain_not_caught_up(
            rpc_address.to_string(),
            chain_id.clone(),
        ));
    }

    let time = response.sync_info.latest_block_time;

    let height = Height::new(
        ChainId::chain_version(response.node_info.network.as_str()),
        u64::from(response.sync_info.latest_block_height),
    )
    .map_err(|_| Error::invalid_height_no_source())?;

    Ok(ChainStatus {
        height,
        timestamp: time.into(),
    })
}
