use async_trait::async_trait;

use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::status::HasChainStatusType;
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct ChainStatusQuerierComponent;

/**
   The provider trait for [`ChainStatusQuerier`].
*/
#[async_trait]
pub trait ChainStatusQuerier<Chain>
where
    Chain: HasChainStatusType + HasErrorType,
{
    async fn query_chain_status(chain: &Chain) -> Result<Chain::ChainStatus, Chain::Error>;
}

#[async_trait]
impl<Chain, Component> ChainStatusQuerier<Chain> for Component
where
    Chain: HasChainStatusType + HasErrorType,
    Component: DelegateComponent<ChainStatusQuerierComponent>,
    Component::Delegate: ChainStatusQuerier<Chain>,
{
    async fn query_chain_status(chain: &Chain) -> Result<Chain::ChainStatus, Chain::Error> {
        Component::Delegate::query_chain_status(chain).await
    }
}

/**
   Implemented by a chain context to provide method for querying the
   [current status](HasChainStatusType::ChainStatus) of the blockchain.
*/
#[async_trait]
pub trait CanQueryChainStatus: HasChainStatusType + HasErrorType {
    /**
        Query the current status of the blockchain. The returned
        [status](HasChainStatusType::ChainStatus) is required to have the same
        or increasing
        [height](crate::chain::traits::types::height::HasHeightType::Height)
        and
        [timestamp](crate::chain::traits::types::timestamp::HasTimestampType::Timestamp)
        each time the query is called.

        The querying of the chain status may fail due to errors such as the full
        node not responding, or from network disconnection.

        TODO: Since the chain status can be queried frequently by the relayer,
        we should implement a cache middleware that cache the result returned
        from the chain query.
    */
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}

#[async_trait]
impl<Chain> CanQueryChainStatus for Chain
where
    Chain: HasChainStatusType + HasErrorType + HasComponents,
    Chain::Components: ChainStatusQuerier<Chain>,
{
    async fn query_chain_status(&self) -> Result<Chain::ChainStatus, Chain::Error> {
        Chain::Components::query_chain_status(self).await
    }
}

#[async_trait]
pub trait CanQueryChainHeight: HasHeightType + HasErrorType {
    async fn query_chain_height(&self) -> Result<Self::Height, Self::Error>;
}

#[async_trait]
impl<Chain> CanQueryChainHeight for Chain
where
    Chain: CanQueryChainStatus,
    Chain::Height: Clone,
{
    async fn query_chain_height(&self) -> Result<Chain::Height, Chain::Error> {
        let status = self.query_chain_status().await?;
        let height = Chain::chain_status_height(&status);
        Ok(height.clone())
    }
}
