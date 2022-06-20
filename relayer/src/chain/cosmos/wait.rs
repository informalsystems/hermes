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
    let num_events = events.len();

    // Check if broadcasting the transaction failed
    if response.code.value() != 0 {
        // Replace the events with errors so we don't attempt to resolve the transaction later on.
        *events = vec![IbcEvent::ChainError(format!(
            "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
            chain_id, response.hash, response.code, response.log
        )); num_events];
        return Ok(());
    }

    // Check if we previously found events for the transaction.
    // If a transaction query results in at least one event then it has been included in a block.
    if empty_event_present(events) {
        // No events for this transaction, query again the transaction by hash.
        let events_per_tx = query_txs(
            chain_id,
            rpc_client,
            rpc_address,
            QueryTxRequest::Transaction(QueryTxHash(response.hash)),
        )
        .await?;

        // Check if the query found the transaction and its events.
        if !events_per_tx.is_empty() {
            // Transaction was included in a block. Check the events.
            let result = events_per_tx
                .iter()
                .find(|event| matches!(event, IbcEvent::ChainError(_)));
            match result {
                // The transaction was successful, copy the events
                None => *events = events_per_tx,

                // The transaction failed deliver_tx. In this case all messages that
                // were included in the transactions are marked as failed.
                // Note: It is possible to extract the `index` from the response.
                // This identifies the message in the transaction that caused the failure.
                // This gives more information on the (first) message that caused the error.
                // There is no evaluation of messages after the first failed message.
                // If n messages are sent in a Tx, and the error index is i then:
                //  - messages 1..i-1 passed deliverTx,
                //  - message i failed deliverTx,
                //  - deliverTx has not run for i+1..n
                // Same is true for checkTx (above)
                // TODO - maybe add at some point more error details to the `IbcEvent::ChainError()`
                // below.
                Some(err) => {
                    *events = vec![
                        IbcEvent::ChainError(format!(
                            "deliver_tx on chain {} for Tx hash {} reports {:?}",
                            chain_id, response.hash, err
                        ));
                        num_events
                    ];
                }
            }
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
