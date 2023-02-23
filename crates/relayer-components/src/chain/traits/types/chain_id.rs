/*!
   Trait definitions for [`HasChainIdType`] and [`HasChainId`].
*/

use crate::base::core::traits::sync::Async;

/**
   This is implemented by a chain context to provide a
   [`ChainId`](Self::ChainId) type that should uniquely identify the chain.

   The relay context uses this information to identify whether an IBC packet
   corresponds to a given chain, based on the chain ID information that is
   queried from a channel ID.

   This trait is automatically implemented by
   [`OfaChainWrapper`](crate::base::one_for_all::types::chain::OfaChainWrapper)
   for a chain context that implements
   [`OfaChainTypes`](crate::base::one_for_all::traits::chain::OfaChainTypes).
   From there, the [`HasChainIdType::ChainId`] type is derived from
   [`OfaChainTypes::ChainId`](crate::base::one_for_all::traits::chain::OfaChainTypes::ChainId).
*/
pub trait HasChainIdType: Async {
    /**
       The ID of a chain, which should implement [`Eq`] to differentiate chain
       ID of two chains with the same type.
    */
    type ChainId: Eq + Async;
}

/**
   This implements the accessor method to get a chain context's
   [chain ID](HasChainIdType::ChainId).

   This trait is automatically implemented by
   [`OfaChainWrapper`](crate::base::one_for_all::types::chain::OfaChainWrapper)
   for a chain context that implements
   [`OfaBaseChain`](crate::base::one_for_all::traits::chain::OfaBaseChain).
   From there, the [`HasChainId::chain_id`] method is derived from
   [`OfaBaseChain::chain_id`](crate::base::one_for_all::traits::chain::OfaBaseChain::chain_id).
*/
pub trait HasChainId: HasChainIdType {
    /**
       Get the ID of a chain context. A chain context is expected to always
       return the same ID. In case there is a chain upgrade, a new chain
       context should be created with the new chain ID.
    */
    fn chain_id(&self) -> &Self::ChainId;
}
