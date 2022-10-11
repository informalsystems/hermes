use core::marker::PhantomData;

use crate::base::chain::traits::context::HasIbcChainTypes;
use crate::base::core::traits::runtime::HasRuntime;
use crate::base::core::traits::runtimes::log::{HasLogger, LevelDebug};
use crate::base::core::traits::runtimes::sleep::CanSleep;
use crate::base::core::traits::runtimes::spawn::HasSpawner;
use crate::base::core::traits::runtimes::time::HasTime;
use crate::base::relay::traits::context::HasRelayTypes;
use crate::base::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

use super::config::BatchConfig;
use super::context::HasBatchContext;
use super::message_sender::HasIbcMessageSenderForBatchWorker;
use super::worker::BatchMessageWorker;

pub struct BatchMessageWorkerSpawner<Target>(PhantomData<Target>);

pub trait CanSpawnBatchMessageWorker<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Relay: HasBatchContext<Target>,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig);
}

impl<Relay, Target, TargetChain, Runtime> CanSpawnBatchMessageWorker<Relay, Target>
    for BatchMessageWorkerSpawner<Target>
where
    Relay: HasRelayTypes,
    Relay: HasRuntime<Runtime = Runtime>,
    Relay: HasIbcMessageSenderForBatchWorker<Target>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Relay: HasBatchContext<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    Relay::Error: Clone,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        <BatchMessageWorker<Relay, Target, Relay::IbcMessageSenderForBatchWorker>>::spawn_batch_message_worker(
            relay,
            config,
        )
    }
}
