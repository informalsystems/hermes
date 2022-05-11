use color_eyre::eyre::Context;
use sqlx::PgPool;
use tracing::info;

use tendermint_proto::abci::TxResult;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::error::ReportError;
use crate::search::TxSearch;
use crate::utils::proto_to_deliver_tx;

#[tracing::instrument(skip(pool))]
pub async fn tx_search(pool: &PgPool, search: TxSearch) -> Result<TxSearchResponse, ReportError> {
    info!(hash = ?search.hash, "got tx_hash");

    let raw_tx_result = tx_result_by_hash(pool, &search.hash).await?;
    let deliver_tx = raw_tx_result.result.unwrap();
    let tx_result = proto_to_deliver_tx(deliver_tx)?;

    dbg!(&tx_result.events);

    let txs = vec![TxResponse {
        hash: search.hash.parse().wrap_err("failed to parse tx hash")?, // TODO: validate hash earlier
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

async fn tx_result_by_hash(pool: &PgPool, hash: &str) -> Result<TxResult, ReportError> {
    use prost::Message;

    let bytes = sqlx::query_scalar::<_, Vec<u8>>(
        "SELECT tx_result FROM tx_results WHERE tx_hash = $1 LIMIT 1",
    )
    .bind(hash)
    .fetch_one(pool)
    .await
    .wrap_err(format!("no tx found with hash '{hash}'"))?;

    let tx_result = tendermint_proto::abci::TxResult::decode(bytes.as_slice())
        .wrap_err("failed to decode tx result")?;

    Ok(tx_result)
}
