use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::core::traits::sync::Async;

/**
   A chain context that offers a [`ChainStatus`](Self::ChainStatus) type to
   contain information about the current status of the chain.

   The `ChainStatus` type contains at minimal a
   [`Height`](crate::base::chain::traits::types::height::HasHeightType::Height)
   field and a
   [`Timestamp`](crate::base::chain::traits::types::timestamp::HasTimestampType::Timestamp)
   field, which are accessible
   via the accessor methods [`chain_status_height`](Self::chain_status_height)
   and [`chain_status_timestamp`](Self::chain_status_timestamp).

   Using context-generic programming, the chain context may also expose
   additional fields to the chain status by introducing additional traits
   containing accessor methods. For example, one may define a
   `HasChainHealthStatus` trait to access the health status information
   from a given chain status.

   The extensible nature of the abstract [`ChainStatus`](Self::ChainStatus)
   type allows the implementation of a caching layer in the future, so that
   chain status queries can be cached without needing to know what information
   is contained inside the chain status.
*/
pub trait HasChainStatusType: HasChainTypes {
    /**
       Contains information about the current status of the blockchain.
    */
    type ChainStatus: Async;

    /**
       Get the blockchain's current
       [height](crate::base::chain::traits::types::height::HasHeightType::Height)
       from the chain status result.
    */
    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    /**
        Get the blockchain's current
        [`Timestamp`](crate::base::chain::traits::types::timestamp::HasTimestampType::Timestamp)
        from the chain status result.
    */
    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;
}
