use async_trait::async_trait;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosChainHandler;
use crate::traits::queries::status::{ChainStatus, ChainStatusQuerier};

impl<Chain> ChainStatus<CosmosChainHandler<Chain>> for CosmosChainStatus
where
    Chain: ChainHandle,
{
    fn height(&self) -> Height {
        self.height
    }

    fn timestamp(&self) -> Timestamp {
        self.timestamp
    }
}

#[async_trait]
impl<Chain> ChainStatusQuerier<CosmosChainHandler<Chain>> for CosmosChainHandler<Chain>
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
