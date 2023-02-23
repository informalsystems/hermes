use async_trait::async_trait;

use crate::chain::traits::types::status::HasChainStatusType;
use crate::std_prelude::*;

/**
   Implemented by a chain context to provide method for querying the
   [current status](HasChainStatusType::ChainStatus) of the blockchain.
*/
#[async_trait]
pub trait CanQueryChainStatus: HasChainStatusType {
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

/**
   The provider trait for [`ChainStatusQuerier`].
*/
#[async_trait]
pub trait ChainStatusQuerier<Chain: HasChainStatusType> {
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error>;
}
