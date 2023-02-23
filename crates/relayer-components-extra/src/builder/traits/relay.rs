use async_trait::async_trait;
use ibc_relayer_components::builder::traits::birelay::HasBiRelayType;
use ibc_relayer_components::builder::traits::target::relay::RelayBuildTarget;
use ibc_relayer_components::builder::types::aliases::{
    TargetDstChain, TargetDstClientId, TargetRelay, TargetSrcChain, TargetSrcClientId,
};
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::mutex::HasRuntimeWithMutex;

use crate::batch::traits::channel::HasMessageBatchSenderTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait RelayBuilderWithBatch<Build, Target>: Async
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    Target: RelayBuildTarget<Build>,
    Target::TargetRelay: HasMessageBatchSenderTypes,
{
    async fn build_relay_with_batch(
        build: &Build,
        target: Target,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
        src_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::SrcMessageBatchSender,
        dst_batch_sender: <Target::TargetRelay as HasMessageBatchSenderTypes>::DstMessageBatchSender,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}
