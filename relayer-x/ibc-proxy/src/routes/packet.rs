use sqlx::PgPool;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::{error::ReportError, search::PacketSearch};

#[tracing::instrument(skip(_pool))]
pub async fn packet_search(
    _pool: &PgPool,
    _search: PacketSearch,
) -> Result<TxSearchResponse, ReportError> {
    todo!()
}
