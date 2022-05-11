use color_eyre::eyre::Context;
use sqlx::PgPool;
use tracing::{info, trace};

use tendermint_proto::abci::TxResult;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::{error::ReportError, routes::tx::proto_to_deliver_tx, search::HeaderSearch};

#[tracing::instrument(skip(pool))]
pub async fn header_search(
    pool: &PgPool,
    search: HeaderSearch,
) -> Result<TxSearchResponse, ReportError> {
    info!(
        client_id = %search.client_id,
        consensus_height = %search.consensus_height,
        "got header search"
    );

    let (raw_tx_result, hash) = tx_result_by_header_fields(pool, search).await?;
    let deliver_tx = raw_tx_result.result.unwrap();
    let tx_result = proto_to_deliver_tx(deliver_tx)?;

    trace!(tx_result.events = ? &tx_result.events, "got events");

    let txs = vec![TxResponse {
        hash: hash.parse().wrap_err("failed to parse tx hash")?, // TODO: validate hash earlier
        height: raw_tx_result.height.try_into().unwrap(),
        index: raw_tx_result.index,
        tx_result,
        tx: raw_tx_result.tx.into(),
        proof: None,
    }];

    Ok(TxSearchResponse {
        txs,
        total_count: 1,
    })
}

#[derive(Debug, sqlx::FromRow)]
struct SqlTxResult {
    tx_hash: String,
    tx_result: Vec<u8>,
}

async fn tx_result_by_header_fields(
    pool: &PgPool,
    search: HeaderSearch,
) -> Result<(TxResult, String), ReportError> {
    use prost::Message;

    let result = sqlx::query_as::<_, SqlTxResult>(
        "SELECT tx_hash, tx_result \
        FROM ibc_tx_client_events WHERE \
        type = $1 and \
        client_id = $2 and \
        consensus_height = $3 \
        LIMIT 1",
    )
    .bind(search.event_type)
    .bind(search.client_id.clone())
    .bind(search.consensus_height.clone())
    .fetch_one(pool)
    .await
    .wrap_err(format!(
        "no tx found with client id '{}' at height {}",
        search.client_id, search.consensus_height
    ))?;

    let tx_result = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
        .wrap_err("failed to decode tx result")?;

    Ok((tx_result, result.tx_hash))
}
