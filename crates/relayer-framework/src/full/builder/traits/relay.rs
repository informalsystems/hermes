use async_trait::async_trait;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::relay::RelayBuildTarget;
use crate::base::builder::types::aliases::{
    TargetDstChain, TargetDstClientId, TargetRelay, TargetRelayError, TargetSrcChain,
    TargetSrcClientId,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::types::aliases::Runtime;
use crate::full::batch::types::aliases::MessageBatchSender;
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait RelayBuilderWithBatch<Build, Target>: Async
where
    Build: HasBiRelayType + HasRuntimeWithMutex + HasErrorType,
    Target: RelayBuildTarget<Build>,
    TargetSrcChain<Build, Target>: HasRuntime,
    TargetDstChain<Build, Target>: HasRuntime,
    Runtime<TargetSrcChain<Build, Target>>: HasChannelTypes + HasChannelOnceTypes,
    Runtime<TargetDstChain<Build, Target>>: HasChannelTypes + HasChannelOnceTypes,
{
    async fn build_relay_with_batch(
        build: &Build,
        target: Target,
        src_client_id: &TargetSrcClientId<Build, Target>,
        dst_client_id: &TargetDstClientId<Build, Target>,
        src_chain: TargetSrcChain<Build, Target>,
        dst_chain: TargetDstChain<Build, Target>,
        src_batch_sender: MessageBatchSender<
            TargetSrcChain<Build, Target>,
            TargetRelayError<Build, Target>,
        >,
        dst_batch_sender: MessageBatchSender<
            TargetDstChain<Build, Target>,
            TargetRelayError<Build, Target>,
        >,
    ) -> Result<TargetRelay<Build, Target>, Build::Error>;
}
