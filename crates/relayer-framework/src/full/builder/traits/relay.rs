use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    TargetDstChain, TargetDstClientId, TargetRelay, TargetSrcChain, TargetSrcClientId,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::full::batch::traits::channel::HasMessageBatchSenderTypes;
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
