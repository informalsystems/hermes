use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::ChainContext;
use crate::traits::core::Async;

pub trait ChainStatus<Context: ChainContext>: Async {
    fn height(&self) -> &Context::Height;

    fn timestamp(&self) -> &Context::Timestamp;
}

pub trait ChainStatusContext: ChainContext {
    type ChainStatus: ChainStatus<Self>;
}

#[async_trait]
pub trait ChainStatusQuerier<Context: ChainStatusContext> {
    async fn query_chain_status(context: &Context) -> Result<Context::ChainStatus, Context::Error>;
}

#[async_trait]
pub trait ChainStatusQuerierContext: ChainStatusContext {
    type ChainStatusQuerier: ChainStatusQuerier<Self>;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Self::ChainStatusQuerier::query_chain_status(self).await
    }
}
