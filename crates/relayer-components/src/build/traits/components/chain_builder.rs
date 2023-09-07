use async_trait::async_trait;

use crate::build::traits::birelay::HasBiRelayType;
use crate::build::traits::target::chain::ChainBuildTarget;
use crate::build::types::aliases::{TargetChain, TargetChainId};
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct ChainBuilderComponent;

#[async_trait]
pub trait ChainBuilder<Build, Target>
where
    Build: HasBiRelayType + HasErrorType,
    Target: ChainBuildTarget<Build>,
{
    async fn build_chain(
        build: &Build,
        chain_id: &TargetChainId<Build, Target>,
    ) -> Result<TargetChain<Build, Target>, Build::Error>;
}

#[async_trait]
impl<Build, Target, Component> ChainBuilder<Build, Target> for Component
where
    Build: HasBiRelayType + HasErrorType,
    Target: ChainBuildTarget<Build>,
    Component: DelegateComponent<ChainBuilderComponent>,
    Component::Delegate: ChainBuilder<Build, Target>,
{
    async fn build_chain(
        build: &Build,
        chain_id: &TargetChainId<Build, Target>,
    ) -> Result<TargetChain<Build, Target>, Build::Error> {
        Component::Delegate::build_chain(build, chain_id).await
    }
}

#[async_trait]
pub trait CanBuildChain<Target>: HasBiRelayType + HasErrorType
where
    Target: ChainBuildTarget<Self>,
{
    async fn build_chain(
        &self,
        _target: Target,
        chain_id: &TargetChainId<Self, Target>,
    ) -> Result<TargetChain<Self, Target>, Self::Error>;
}

#[async_trait]
impl<Build, Target> CanBuildChain<Target> for Build
where
    Build: HasBiRelayType + HasErrorType + HasComponents,
    Target: ChainBuildTarget<Build>,
    Build::Components: ChainBuilder<Build, Target>,
{
    async fn build_chain(
        &self,
        _target: Target,
        chain_id: &TargetChainId<Self, Target>,
    ) -> Result<TargetChain<Self, Target>, Self::Error> {
        Build::Components::build_chain(self, chain_id).await
    }
}
