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

pub trait HasBatchSenderCache<Target, Error>: Async
where
    Target: HasBatchSenderCacheType<Self, Error>,
{
    fn batch_sender_cache(
        &self,
        target: Target,
    ) -> &<Target as HasBatchSenderCacheType<Self, Error>>::BatchSenderCache;
}

pub trait HasBatchSenderCacheType<Build, Error>: Async {
    type BatchSenderCache: Async;
}

impl<Target, Build, Error> HasBatchSenderCacheType<Build, Error> for Target
where
    Error: Async,
    Build: HasBiRelayType + HasRuntimeWithMutex,
    Target: ChainBuildTarget<Build>,
    Target::TargetChain: HasMessageBatchSenderType<Error>,
{
    type BatchSenderCache = Arc<
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
}
