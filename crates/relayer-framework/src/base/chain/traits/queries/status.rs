use async_trait::async_trait;

use crate::base::chain::traits::context::HasChainTypes;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasChainStatus: HasChainTypes {
    type ChainStatus: Async;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;
}

#[async_trait]
pub trait ChainStatusQuerier<Chain: HasChainStatus> {
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error>;
}

#[async_trait]
pub trait HasChainStatusQuerier: HasChainStatus {
    type ChainStatusQuerier: ChainStatusQuerier<Self>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Self::ChainStatusQuerier::query_chain_status(self).await
    }
}
