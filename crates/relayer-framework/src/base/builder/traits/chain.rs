use async_trait::async_trait;

use crate::base::builder::traits::target::chain::HasChainBuildTarget;
use crate::base::builder::types::aliases::{TargetChain, TargetChainId};
use crate::base::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChain<Target>: HasChainBuildTarget<Target> + HasErrorType {
    async fn build_chain(
        &self,
        target: Target,
        chain_id: &TargetChainId<Self, Target>,
    ) -> Result<TargetChain<Self, Target>, Self::Error>;
}

#[async_trait]
pub trait ChainBuilder<Builder, Target>
where
    Builder: HasChainBuildTarget<Target> + HasErrorType,
{
    async fn build_chain(
        builder: &Builder,
        chain_id: &TargetChainId<Builder, Target>,
    ) -> Result<TargetChain<Builder, Target>, Builder::Error>;
}
