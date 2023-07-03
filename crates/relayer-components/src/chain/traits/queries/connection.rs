use async_trait::async_trait;

use crate::chain::traits::types::connection::{HasConnectionDetailsType, HasConnectionVersionType};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryConnectionDetails<Counterparty>:
    HasConnectionDetailsType<Counterparty> + HasErrorType
{
    async fn query_connection_details(
        &self,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionDetails, Self::Error>;
}

#[async_trait]
pub trait CanQueryCompatibleConnectionVersions<Counterparty>:
    HasConnectionVersionType<Counterparty> + HasErrorType
{
    async fn query_compatible_connection_versions(
        &self,
    ) -> Result<Vec<Self::ConnectionVersion>, Self::Error>;
}
