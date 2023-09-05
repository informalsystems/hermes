use async_trait::async_trait;
use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;
use ibc_relayer_components::builder::traits::target::relay::RelayBuildTarget;
use ibc_relayer_components::builder::types::aliases::{
    TargetDstChain, TargetDstClientId, TargetRelay, TargetSrcChain, TargetSrcClientId,
};
use ibc_relayer_components::core::traits::component::{DelegateComponent, HasComponents};
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::runtime::traits::mutex::HasRuntimeWithMutex;

use crate::batch::traits::channel::HasMessageBatchSenderTypes;
use crate::std_prelude::*;

pub struct RelayWithBatchBuilderComponent;

#[async_trait]
pub trait RelayWithBatchBuilder<Build, Target>
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    Target: RelayBuildTarget<Build>,
    Target::TargetRelay: HasMessageBatchSenderTypes,
{
    async fn build_relay_with_batch(
        build: &Build,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
        src_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::SrcMessageBatchSender,
        dst_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::DstMessageBatchSender,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}

#[async_trait]
impl<Build, Target, Component> RelayWithBatchBuilder<Build, Target> for Component
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    Target: RelayBuildTarget<Build>,
    Target::TargetRelay: HasMessageBatchSenderTypes,
    Component: DelegateComponent<RelayWithBatchBuilderComponent>,
    Component::Delegate: RelayWithBatchBuilder<Build, Target>,
{
    async fn build_relay_with_batch(
        build: &Build,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
        src_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::SrcMessageBatchSender,
        dst_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::DstMessageBatchSender,
    ) -> Result<TargetRelay<Build, Target>, Build::Error> {
        Component::Delegate::build_relay_with_batch(
            build,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await
    }
}

#[async_trait]
pub trait CanBuildRelayWithBatch<Target>:
    HasBiRelayType + HasRuntimeWithMutex + HasErrorType
where
    Target: RelayBuildTarget<Self>,
    Target::TargetRelay: HasMessageBatchSenderTypes,
{
    async fn build_relay_with_batch(
        &self,
        target: Target,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
        src_chain: TargetSrcChain<Self, Target>,
        dst_chain: TargetDstChain<Self, Target>,
        src_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::SrcMessageBatchSender,
        dst_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::DstMessageBatchSender,
    ) -> Result<TargetRelay<Self, Target>, Self::Error>;
}

#[async_trait]
impl<Build, Target> CanBuildRelayWithBatch<Target> for Build
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType + HasComponents,
    Target: RelayBuildTarget<Build>,
    Target::TargetRelay: HasMessageBatchSenderTypes,
    Build::Components: RelayWithBatchBuilder<Build, Target>,
{
    async fn build_relay_with_batch(
        &self,
        _target: Target,
        src_client_id: &TargetSrcClientId<Self, Target>,
        dst_client_id: &TargetDstClientId<Self, Target>,
        src_chain: TargetSrcChain<Self, Target>,
        dst_chain: TargetDstChain<Self, Target>,
        src_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::SrcMessageBatchSender,
        dst_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::DstMessageBatchSender,
    ) -> Result<TargetRelay<Self, Target>, Self::Error> {
        Build::Components::build_relay_with_batch(
            self,
            src_client_id,
            dst_client_id,
            src_chain,
            dst_chain,
            src_batch_sender,
            dst_batch_sender,
        )
        .await
    }
}
