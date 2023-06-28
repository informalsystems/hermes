use async_trait::async_trait;

use crate::chain::traits::types::connection::HasConnectionDetailsType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryConnection<Counterparty>:
    HasConnectionDetailsType<Counterparty> + HasErrorType
{
    async fn query_connection(
        &self,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionDetails, Self::Error>;
}
