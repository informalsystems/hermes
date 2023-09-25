use alloc::collections::BTreeMap;

use ibc_relayer_components::build::traits::birelay::HasBiRelayType;
use ibc_relayer_components::build::traits::target::chain::ChainBuildTarget;
use ibc_relayer_components::build::types::aliases::{
    CounterpartyChainId, CounterpartyClientId, TargetChain, TargetChainId, TargetClientId,
};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::mutex::HasRuntimeWithMutex;
use ibc_relayer_components::runtime::types::aliases::Mutex;

use crate::batch::traits::channel::HasMessageBatchSenderType;

pub trait HasBatchSenderCache<Target, Error>: Async
where
    Target: HasBatchSenderCacheType<Self, Error>,
{
    fn batch_sender_cache(&self, target: Target) -> &Target::BatchSenderCache;
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
    type BatchSenderCache = Mutex<
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
    >;
}
