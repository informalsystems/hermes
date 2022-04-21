use core::time::Duration;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;
use ibc::query::{QueryTxHash, QueryTxRequest};
use itertools::Itertools;
use std::thread;
use std::time::Instant;
use tendermint_rpc::{HttpClient, Url};
use tracing::{info, trace};

use crate::chain::cosmos::query::tx::query_txs;
use crate::chain::cosmos::types::tx::TxSyncResult;
use crate::error::Error;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

/// Given a vector of `TxSyncResult` elements,
/// each including a transaction response hash for one or more messages, periodically queries the chain
/// with the transaction hashes to get the list of IbcEvents included in those transactions.
pub async fn wait_for_block_commits(
    chain_id: &ChainId,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    rpc_timeout: &Duration,
    tx_sync_results: &mut [TxSyncResult],
) -> Result<(), Error> {
    let start_time = Instant::now();

    let hashes = tx_sync_results
        .iter()
        .map(|res| res.response.hash.to_string())
        .join(", ");

    info!(
        id = %chain_id,
        "wait_for_block_commits: waiting for commit of tx hashes(s) {}",
        hashes
    );

    loop {
        let elapsed = start_time.elapsed();

        if all_tx_results_found(tx_sync_results) {
            trace!(
                id = %chain_id,
                "wait_for_block_commits: retrieved {} tx results after {}ms",
                tx_sync_results.len(),
                elapsed.as_millis(),
            );

            return Ok(());
        } else if &elapsed > rpc_timeout {
            return Err(Error::tx_no_confirmation());
        } else {
            thread::sleep(WAIT_BACKOFF);

            for tx_sync_result in tx_sync_results.iter_mut() {
                // ignore error
                let _ =
                    update_tx_sync_result(chain_id, rpc_client, rpc_address, tx_sync_result).await;
            }
        }
    }
}

async fn update_tx_sync_result(
    chain_id: &ChainId,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    tx_sync_result: &mut TxSyncResult,
) -> Result<(), Error> {
    let TxSyncResult { response, events } = tx_sync_result;

    // If this transaction was not committed, determine whether it was because it failed
    // or because it hasn't been committed yet.
    if empty_event_present(events) {
        // If the transaction failed, replace the events with an error,
        // so that we don't attempt to resolve the transaction later on.
        if response.code.value() != 0 {
            *events = vec![IbcEvent::ChainError(format!(
                "deliver_tx on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                chain_id, response.hash, response.code, response.log
            ))];
        }

        // Otherwise, try to resolve transaction hash to the corresponding events.
        let events_per_tx = query_txs(
            chain_id,
            rpc_client,
            rpc_address,
            QueryTxRequest::Transaction(QueryTxHash(response.hash)),
        )
        .await?;

        // If we get events back, progress was made, so we replace the events
        // with the new ones. in both cases we will check in the next iteration
        // whether or not the transaction was fully committed.
        if !events_per_tx.is_empty() {
            *events = events_per_tx;
        }
    }

    Ok(())
}

fn empty_event_present(events: &[IbcEvent]) -> bool {
    events.iter().any(|ev| matches!(ev, IbcEvent::Empty(_)))
}

fn all_tx_results_found(tx_sync_results: &[TxSyncResult]) -> bool {
    tx_sync_results
        .iter()
        .all(|r| !empty_event_present(&r.events))
}
