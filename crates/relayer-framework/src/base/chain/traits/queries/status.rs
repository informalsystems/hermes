use async_trait::async_trait;

use crate::base::chain::traits::types::status::HasChainStatusType;
use crate::std_prelude::*;

#[async_trait]
pub trait ChainStatusQuerier<Chain: HasChainStatusType> {
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error>;
}

#[async_trait]
pub trait CanQueryChainStatus: HasChainStatusType {
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}
