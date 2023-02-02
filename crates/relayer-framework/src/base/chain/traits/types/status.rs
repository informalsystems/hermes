use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::core::traits::sync::Async;

/// Chains that implement this trait expose a `ChainStatus` type that, at
/// minimum, exposes the chain's height and timestamp.
pub trait HasChainStatusType: HasChainTypes {
    type ChainStatus: Async;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;
}
