use core::time::Duration;
use std::thread;
use std::time::Instant;

use itertools::Itertools;
use sqlx::PgPool;
use tracing::{info, trace};

use crate::chain::cosmos::types::config::TxConfig;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::psql_cosmos::query::query_hashes_and_update_tx_sync_results;
use crate::error::Error;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

/// Given a vector of `TxSyncResult` elements,
/// each including a transaction response hash for one or more messages, periodically queries the chain
/// with the transaction hashes to get the list of IbcEvents included in those transactions.
pub async fn wait_for_block_commits(
    pool: &PgPool,
    config: &TxConfig,
    tx_sync_results: &mut [TxSyncResult],
) -> Result<(), Error> {
    let start_time = Instant::now();

    let hashes = tx_sync_results
        .iter()
        .map(|res| res.response.hash.to_string())
        .join(", ");

    info!(
        id = %config.chain_id,
        "wait_for_block_commits: waiting for commit of tx hashes(s) {}",
        hashes
    );

    loop {
        let elapsed = start_time.elapsed();

        if all_tx_results_found(tx_sync_results) {
            trace!(
                id = %config.chain_id,
                "wait_for_block_commits: retrieved {} tx results after {}ms",
                tx_sync_results.len(),
                elapsed.as_millis(),
            );
            return Ok(());
        }

        if elapsed > config.rpc_timeout {
            return Err(Error::tx_no_confirmation());
        }
        thread::sleep(WAIT_BACKOFF);

        query_hashes_and_update_tx_sync_results(pool, &config.chain_id, tx_sync_results).await?;
    }
}

fn all_tx_results_found(tx_sync_results: &[TxSyncResult]) -> bool {
    tx_sync_results
        .iter()
        .all(|r| matches!(r.status, TxStatus::ReceivedResponse))
}
