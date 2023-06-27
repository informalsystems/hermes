use async_trait::async_trait;

use crate::chain::traits::types::connection::HasConnectionEndType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryConnection<Counterparty>:
    HasConnectionEndType<Counterparty> + HasErrorType
{
    async fn query_connection(
        &self,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionEnd, Self::Error>;
}
