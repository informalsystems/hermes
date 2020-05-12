use relayer_modules::Height;
use crate::chain::Chain;

use super::ibc_query;
use relayer_modules::ics03_connection::QueryConnection;

use relayer_modules::error;

pub async fn query_connection<C>(
    chain: &C,
    chain_height: Height,
    connection_id: String,
    prove: bool,
) -> Result<ConnectionResponse, error::Error>
where
    C: Chain,
{
    let query = QueryConnection::new(chain_height, connection_id, prove);
    ibc_query(chain, query).await
}