use async_trait::async_trait;

use crate::build::traits::birelay::HasBiRelayType;
use crate::build::traits::target::relay::RelayBuildTarget;
use crate::build::types::aliases::{
    TargetDstChainId, TargetDstClientId, TargetRelay, TargetSrcChainId, TargetSrcClientId,
};
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

pub struct RelayBuilderComponent;

#[async_trait]
pub trait RelayBuilder<Build, Target>
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
{
    async fn build_relay(
        build: &Build,
        target: Target,
        src_chain_id: &TargetSrcChainId<Build, Target>,
        dst_chain_id: &TargetDstChainId<Build, Target>,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}

#[async_trait]
impl<Build, Target, Component> RelayBuilder<Build, Target> for Component
where
    Build: HasBiRelayType + HasErrorType,
    Target: RelayBuildTarget<Build>,
    Component: DelegateComponent<RelayBuilderComponent>,
    Component::Delegate: RelayBuilder<Build, Target>,
{
    async fn build_relay(
        build: &Build,
        target: Target,
        src_chain_id: &TargetSrcChainId<Build, Target>,
        dst_chain_id: &TargetDstChainId<Build, Target>,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
    ) -> Result<TargetRelay<Build, Target>, Build::Error> {
        Component::Delegate::build_relay(
            build,
            target,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}

#[async_trait]
pub trait CanBuildRelay<Target>: HasBiRelayType + HasErrorType
where
    Target: RelayBuildTarget<Self>,
{
    async fn build_relay(
        &self,
        target: Target,
        src_chain_id: &TargetSrcChainId<Self, Target>,
        dst_chain_id: &TargetDstChainId<Self, Target>,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
    ) -> Result<TargetRelay<Self, Target>, Self::Error>;
}

#[async_trait]
impl<Build, Target> CanBuildRelay<Target> for Build
where
    Build: HasBiRelayType + HasErrorType + HasComponents,
    Target: RelayBuildTarget<Build>,
    Build::Components: RelayBuilder<Build, Target>,
{
    async fn build_relay(
        &self,
        target: Target,
        src_chain_id: &TargetSrcChainId<Self, Target>,
        dst_chain_id: &TargetDstChainId<Self, Target>,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
    ) -> Result<TargetRelay<Self, Target>, Self::Error> {
        Build::Components::build_relay(
            self,
            target,
            src_chain_id,
            dst_chain_id,
            src_client_id,
            dst_client_id,
        )
        .await
    }
}
