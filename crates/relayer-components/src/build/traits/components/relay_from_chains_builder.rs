use async_trait::async_trait;

use crate::build::traits::birelay::HasBiRelayType;
use crate::build::traits::target::relay::RelayBuildTarget;
use crate::build::types::aliases::{
    TargetDstChain, TargetDstClientId, TargetRelay, TargetSrcChain, TargetSrcClientId,
};
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct RelayFromChainsBuilderComponent;

#[async_trait]
pub trait RelayFromChainsBuilder<Build, Target>
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
{
    async fn build_relay_from_chains(
        build: &Build,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}

#[async_trait]
impl<Build, Target, Component> RelayFromChainsBuilder<Build, Target> for Component
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
    Component: DelegateComponent<RelayFromChainsBuilderComponent>,
    Component::Delegate: RelayFromChainsBuilder<Build, Target>,
{
    async fn build_relay_from_chains(
        build: &Build,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error> {
        Component::Delegate::build_relay_from_chains(
            build,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await
    }
}

#[async_trait]
pub trait CanBuildRelayFromChains<Target>: HasBiRelayType + HasErrorType
where
    Target: RelayBuildTarget<Self>,
{
    async fn build_relay_from_chains(
        &self,
        target: Target,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
        src_chain: TargetSrcChain<Self, Target>,
        dst_chain: TargetDstChain<Self, Target>,
    ) -> Result<TargetRelay<Self, Target>, Self::Error>;
}

#[async_trait]
impl<Build, Target> CanBuildRelayFromChains<Target> for Build
where
    Build: HasBiRelayType + HasErrorType + HasComponents,
    Target: RelayBuildTarget<Build>,
    Build::Components: RelayFromChainsBuilder<Build, Target>,
{
    async fn build_relay_from_chains(
        &self,
        _target: Target,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
        src_chain: TargetSrcChain<Self, Target>,
        dst_chain: TargetDstChain<Self, Target>,
    ) -> Result<TargetRelay<Self, Target>, Self::Error> {
        Build::Components::build_relay_from_chains(
            self,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
        )
        .await
    }
}
