use color_eyre::eyre::Context;
use sqlx::PgPool;
use tracing::{info, trace};

use tendermint_proto::abci::TxResult;
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::utils::proto_to_deliver_tx;
use crate::{error::ReportError, search::PacketSearch};

#[tracing::instrument(skip(pool))]
pub async fn packet_search(
    pool: &PgPool,
    search: PacketSearch,
) -> Result<TxSearchResponse, ReportError> {
    info!(seq = ?search.packet_sequence, "got sequence");

    let (raw_tx_result, hash) = tx_result_by_packet_fields(pool, search).await?;
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

async fn tx_result_by_packet_fields(
    pool: &PgPool,
    search: PacketSearch,
) -> Result<(TxResult, String), ReportError> {
    use prost::Message;

    let result = sqlx::query_as::<_, SqlTxResult>(
        "SELECT tx_hash, tx_result FROM ibc_tx_packet_events WHERE \
        packet_sequence = $1 and \
        type = $2 and \
        packet_src_channel = $3 and \
        packet_src_port = $4 \
        LIMIT 1",
    )
    .bind(search.packet_sequence.clone())
    .bind(search.event_type)
    .bind(search.packet_src_channel)
    .bind(search.packet_src_port)
    .fetch_one(pool)
    .await
    .wrap_err(format!(
        "no tx found with sequence '{}'",
        search.packet_sequence
    ))?;

    let tx_result = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
        .wrap_err("failed to decode tx result")?;

    Ok((tx_result, result.tx_hash))
}
