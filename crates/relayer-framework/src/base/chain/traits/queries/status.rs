use async_trait::async_trait;

use crate::base::chain::traits::types::HasChainTypes;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

/// Chains that implement this trait expose a `ChainStatus` type that, at
/// minimum, exposes the chain's height and timestamp.
pub trait HasChainStatus: HasChainTypes {
    type ChainStatus: Async;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;
}

#[async_trait]
pub trait ChainStatusQuerier<Chain: HasChainStatus> {
    async fn query_chain_status(context: &Chain) -> Result<Chain::ChainStatus, Chain::Error>;
}

#[async_trait]
pub trait CanQueryChainStatus: HasChainStatus {
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;
}
