use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_components::core::traits::sync::Async;

use crate::contexts::chain::CosmosChain;
use crate::types::error::{BaseError, Error};

#[async_trait]
pub trait HasBlockingChainHandle: Async {
    type ChainHandle: ChainHandle;

    async fn with_blocking_chain_handle<R>(
        &self,
        cont: impl FnOnce(Self::ChainHandle) -> Result<R, Error> + Send + 'static,
    ) -> Result<R, Error>
    where
        R: Send + 'static;
}

#[async_trait]
impl<Chain> HasBlockingChainHandle for CosmosChain<Chain>
where
    Chain: ChainHandle,
{
    type ChainHandle = Chain;

    async fn with_blocking_chain_handle<R>(
        &self,
        cont: impl FnOnce(Chain) -> Result<R, Error> + Send + 'static,
    ) -> Result<R, Error>
    where
        R: Send + 'static,
    {
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .spawn_blocking(move || cont(chain_handle))
            .await
            .map_err(BaseError::join)?
    }
}
