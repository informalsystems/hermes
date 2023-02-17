use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::types::aliases::{TargetChain, TargetChainId};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChain<Target>: HasBiRelayType + HasErrorType
where
    Target: ChainBuildTarget<Self>,
{
    async fn build_chain(
        &self,
        target: Target,
        chain_id: &TargetChainId<Self, Target>,
    ) -> Result<TargetChain<Self, Target>, Self::Error>;
}

#[async_trait]
pub trait ChainBuilder<Builder, Target>
where
    Builder: HasBiRelayType + HasErrorType,
    Target: ChainBuildTarget<Builder>,
{
    async fn build_chain(
        builder: &Builder,
        target: Target,
        chain_id: &TargetChainId<Builder, Target>,
    ) -> Result<TargetChain<Builder, Target>, Builder::Error>;
}
