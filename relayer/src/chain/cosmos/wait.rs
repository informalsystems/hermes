use core::time::Duration;
use futures::stream::{FuturesOrdered, StreamExt};
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;
use itertools::Itertools;
use std::thread;
use std::time::Instant;
use tendermint::abci::transaction::Hash as TxHash;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;
use tendermint_rpc::{HttpClient, Url};
use tokio::time::sleep;
use tracing::info;

use crate::chain::cosmos::query::tx::{all_ibc_events_from_tx_search_response, query_tx_response};
use crate::chain::cosmos::types::tx::TxSyncResult;
use crate::chain::requests::{QueryTxHash, QueryTxRequest};
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

    let all_events = responses
        .into_iter()
        .flat_map(|response| {
            response.txs.into_iter().flat_map(|tx_response| {
                all_ibc_events_from_tx_search_response(chain_id, tx_response)
            })
        })
        .collect();

    Ok(all_events)
}

pub async fn wait_tx_hashes(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hashes: &[TxHash],
) -> Result<Vec<TxSearchResponse>, Error> {
    let tasks = tx_hashes
        .iter()
        .map(|tx_hash| async { wait_tx_hash(rpc_client, rpc_address, timeout, tx_hash).await })
        .collect::<FuturesOrdered<_>>();

    let responses = tasks
        .collect::<Vec<_>>()
        .await
        .into_iter()
        .collect::<Result<Vec<_>, _>>()?;

    Ok(responses)
}

pub async fn wait_tx_succeed(
    rpc_client: &HttpClient,
    rpc_address: &Url,
    timeout: &Duration,
    tx_hash: &TxHash,
) -> Result<Vec<TxResponse>, Error> {
    let response = wait_tx_hash(rpc_client, rpc_address, timeout, tx_hash).await?;

    for response in response.txs.iter() {
        let response_code = response.tx_result.code;
        if response_code.is_err() {
            return Err(Error::rpc_response(format!("{}", response_code.value())));
        }
    }

    Ok(response.txs)
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
