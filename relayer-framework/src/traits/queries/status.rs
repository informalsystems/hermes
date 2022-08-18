use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::chain::ChainContext;
use crate::traits::core::Async;

pub trait ChainStatus<Chain: ChainContext>: Async {
    fn height(&self) -> &Chain::Height;

    fn timestamp(&self) -> &Chain::Timestamp;
}

pub trait HasChainStatus: ChainContext {
    type ChainStatus: ChainStatus<Self>;
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
