use core::time::Duration;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height;
use itertools::Itertools;
use std::thread;
use std::time::Instant;
use tendermint::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::{HttpClient, Url};
use tokio::time::sleep;
use tracing::{debug, debug_span, trace};

use crate::chain::cosmos::query::tx::query_tx_response;
use crate::chain::cosmos::types::events::from_tx_response_event;
use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::error::Error;
use crate::event::IbcEventWithHeight;

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
    if all_tx_results_found(tx_sync_results) {
        return Ok(());
    }

    let _span = debug_span!("wait_for_block_commits", id = %chain_id).entered();

    let start_time = Instant::now();

    let hashes = tx_sync_results
        .iter()
        .map(|res| res.response.hash.to_string())
        .join(", ");

    debug!("waiting for commit of tx hashes(s) {}", hashes);

    loop {
        let elapsed = start_time.elapsed();

        if all_tx_results_found(tx_sync_results) {
            trace!(
                "retrieved {} tx results after {} ms",
                tx_sync_results.len(),
                elapsed.as_millis(),
            );

            return Ok(());
        } else if &elapsed > rpc_timeout {
            debug!("timed out after {} ms", elapsed.as_millis());
            return Err(Error::tx_no_confirmation());
        } else {
            thread::sleep(WAIT_BACKOFF);

            for tx_sync_result in tx_sync_results.iter_mut() {
                let res =
                    update_tx_sync_result(chain_id, rpc_client, rpc_address, tx_sync_result).await;
                if let Err(e) = res {
                    debug!("update_tx_sync_result failed: {e}");
                }
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
    if let TxStatus::Pending { message_count } = tx_sync_result.status {
        let response =
            query_tx_response(rpc_client, rpc_address, &tx_sync_result.response.hash).await?;

        if let Some(response) = response {
            tx_sync_result.status = TxStatus::ReceivedResponse;

            let height = Height::new(chain_id.version(), u64::from(response.height)).unwrap();
            if response.tx_result.code.is_err() {
                tx_sync_result.events = vec![
                    IbcEventWithHeight::new(
                        IbcEvent::ChainError(format!(
                            "deliver_tx for {} reports error: code={:?}, log={:?}",
                            response.hash, response.tx_result.code, response.tx_result.log
                        )),
                        height
                    );
                    message_count
                ];
            } else {
                tx_sync_result.events = response
                    .tx_result
                    .events
                    .iter()
                    .flat_map(|event| from_tx_response_event(height, event))
                    .collect::<Vec<_>>();
            }
        }
    }

    Ok(())
}

fn all_tx_results_found(tx_sync_results: &[TxSyncResult]) -> bool {
    tx_sync_results
        .iter()
        .all(|r| matches!(r.status, TxStatus::ReceivedResponse))
}

pub async fn wait_tx_succeed(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hash: &TxHash,
) -> Result<TxResponse, Error> {
    let response = wait_tx_hash(rpc_client, rpc_address, timeout, tx_hash).await?;

    let response_code = response.tx_result.code;
    if response_code.is_err() {
        return Err(Error::rpc_response(format!("{}", response_code.value())));
    }

    Ok(response)
}

pub async fn wait_tx_hash(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hash: &TxHash,
) -> Result<TxResponse, Error> {
    let start_time = Instant::now();

    loop {
        let response = query_tx_response(rpc_client, rpc_address, tx_hash).await?;

        match response {
            None => {
                let elapsed = start_time.elapsed();
                if &elapsed > timeout {
                    return Err(Error::tx_no_confirmation());
                } else {
                    sleep(WAIT_BACKOFF).await;
                }
            }
            Some(response) => {
                return Ok(response);
            }
        }
    }
}
