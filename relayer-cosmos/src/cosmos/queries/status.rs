use async_trait::async_trait;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::queries::status::{
    ChainStatus, ChainStatusContext, ChainStatusQuerier, ChainStatusQuerierContext,
};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::error::Error;

pub struct CosmosChainStatusQuerier;

impl<Chain> ChainStatus<CosmosChainContext<Chain>> for CosmosChainStatus
where
    Chain: Async,
{
    fn height(&self) -> Height {
        self.height
    }

    fn timestamp(&self) -> Timestamp {
        self.timestamp
    }
}

impl<Chain: ChainHandle> ChainStatusContext for CosmosChainContext<Chain> {
    type ChainStatus = CosmosChainStatus;
}

impl<Chain: ChainHandle> ChainStatusQuerierContext for CosmosChainContext<Chain> {
    type ChainStatusQuerier = CosmosChainStatusQuerier;
}

#[async_trait]
impl<Chain> ChainStatusQuerier<CosmosChainContext<Chain>> for CosmosChainStatusQuerier
where
    Chain: ChainHandle,
{
    async fn query_chain_status(
        context: &CosmosChainContext<Chain>,
    ) -> Result<CosmosChainStatus, Error> {
        let status = context
            .handle
            .query_application_status()
            .map_err(Error::relayer)?;

        Ok(status)
    }
}
