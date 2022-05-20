use core::time::Duration;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;
use std::time::Instant;
use tendermint_rpc::abci::transaction::Hash as TxHash;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;
use tendermint_rpc::{HttpClient, Url};
use tokio::task;
use tokio::time::sleep;
use tracing::info;

use crate::chain::cosmos::query::tx::{all_ibc_events_from_tx_search_response, query_tx_response};
use crate::error::Error;

const WAIT_BACKOFF: Duration = Duration::from_millis(300);

/// Given a vector of `TxHash` elements,
/// each including a transaction response hash for one or more messages, periodically queries the chain
/// with the transaction hashes to get the list of IbcEvents included in those transactions.
pub async fn wait_for_block_commits(
    chain_id: &ChainId,
    rpc_client: &HttpClient,
    rpc_address: &Url,
    rpc_timeout: &Duration,
    tx_hashes: &[TxHash],
) -> Result<Vec<IbcEvent>, Error> {
    info!(
        id = %chain_id,
        "wait_for_block_commits: waiting for commit of tx hashes(s) {:?}",
        tx_hashes
    );

    let responses = wait_tx_hashes(rpc_client, rpc_address, rpc_timeout, tx_hashes).await?;

    let mut all_events = Vec::new();

    for response in responses.into_iter() {
        for tx_response in response.txs.into_iter() {
            let mut events = all_ibc_events_from_tx_search_response(chain_id, tx_response);
            all_events.append(&mut events);
        }
    }

    Ok(all_events)
}

pub async fn wait_tx_hashes(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hashes: &[TxHash],
) -> Result<Vec<TxSearchResponse>, Error> {
    let mut join_handles = Vec::new();

    for tx_hash in tx_hashes.iter() {
        let rpc_client = rpc_client.clone();
        let rpc_address = rpc_address.clone();
        let timeout = *timeout;
        let tx_hash = *tx_hash;

        let handle = task::spawn(async move {
            wait_tx_hash(&rpc_client, &rpc_address, &timeout, &tx_hash).await
        });
        join_handles.push(handle);
    }

    let mut responses = Vec::new();

    for handle in join_handles.into_iter() {
        let response = handle.await.map_err(Error::join)??;
        responses.push(response);
    }

    Ok(responses)
}

pub async fn wait_tx_succeed(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hash: &TxHash,
) -> Result<(), Error> {
    let response = wait_tx_hash(rpc_client, rpc_address, timeout, tx_hash).await?;

    for response in response.txs {
        let response_code = response.tx_result.code;
        if response_code.is_err() {
            return Err(Error::rpc_response(format!("{}", response_code.value())));
        }
    }

    Ok(())
}

pub async fn wait_tx_hash(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hash: &TxHash,
) -> Result<TxSearchResponse, Error> {
    let start_time = Instant::now();

    loop {
        let responses = query_tx_response(rpc_client, rpc_address, tx_hash).await?;

        if responses.txs.is_empty() {
            let elapsed = start_time.elapsed();
            if &elapsed > timeout {
                return Err(Error::tx_no_confirmation());
            } else {
                sleep(WAIT_BACKOFF).await;
            }
        } else {
            return Ok(responses);
        }
    }
}
