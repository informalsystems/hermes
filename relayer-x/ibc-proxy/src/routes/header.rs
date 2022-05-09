use sqlx::PgPool;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::{error::ReportError, search::HeaderSearch};

#[tracing::instrument(skip(_pool))]
pub async fn header_search(
    _pool: &PgPool,
    _search: HeaderSearch,
) -> Result<TxSearchResponse, ReportError> {
    todo!()
}
