use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::builder::traits::target::chain::ChainBuildTarget;
use crate::base::builder::types::aliases::{
    CounterpartyChainId, CounterpartyClientId, TargetChain, TargetChainId, TargetClientId,
};
use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasRuntimeWithMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::types::aliases::{Mutex, Runtime};
use crate::full::batch::types::aliases::MessageBatchSender;
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;

pub trait HasBatchSenderCache<Target, Error>: HasBiRelayType + HasRuntimeWithMutex
where
    Error: Async,
    Target: ChainBuildTarget<Self>,
    TargetChain<Self, Target>: HasRuntime,
    Runtime<TargetChain<Self, Target>>: HasChannelTypes + HasChannelOnceTypes,
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
            MessageBatchSender<TargetChain<Build, Target>, Error>,
        >,
    >,
>;
