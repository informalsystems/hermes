use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::types::aliases::{
    CounterpartyChainId, CounterpartyClientId, TargetChain, TargetChainId, TargetClientId,
};
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::base::runtime::types::aliases::Mutex;
use crate::full::batch::traits::channel::HasMessageBatchSenderType;

pub trait HasBatchSenderCache<Target, Error>: HasBiRelayType + HasRuntimeWithMutex
where
    Error: Async,
    Target: ChainBuildTarget<Self>,
    Target::TargetChain: HasMessageBatchSenderType<Error>,
{
    fn batch_sender_cache(&self, target: Target) -> &BatchSenderCache<Self, Target, Error>;
}

pub type BatchSenderCache<Build, Target, Error> = Arc<
    Mutex<
        Build,
        BTreeMap<
            (
                TargetChainId<Build, Target>,
                CounterpartyChainId<Build, Target>,
                TargetClientId<Build, Target>,
                CounterpartyClientId<Build, Target>,
            ),
            <TargetChain<Build, Target> as HasMessageBatchSenderType<Error>>::MessageBatchSender,
        >,
    >,
>;
