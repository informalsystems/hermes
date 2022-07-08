use async_trait::async_trait;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::queries::status::{ChainStatus, ChainStatusQuerier};

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosChainHandler;

impl<Chain> ChainStatus<CosmosChainHandler<Chain>> for CosmosChainStatus
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

#[async_trait]
impl<Chain> ChainStatusQuerier for CosmosChainHandler<Chain>
where
    Chain: ChainHandle,
{
    type ChainStatus = CosmosChainStatus;

    async fn query_chain_status(&self) -> Result<CosmosChainStatus, Error> {
        let status = self
            .handle
            .query_application_status()
            .map_err(Error::relayer)?;

        Ok(status)
    }
}
