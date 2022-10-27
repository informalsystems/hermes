use core::marker::PhantomData;

use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::log::{HasLogger, LevelDebug};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::spawn::HasSpawner;
use crate::base::runtime::traits::time::HasTime;
use crate::std_prelude::*;

use super::config::BatchConfig;
use super::context::HasBatchContext;
use super::message_sender::CanSendIbcMessagesFromBatchWorker;
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
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Relay: HasBatchContext<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    Relay::Error: Clone,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        <BatchMessageWorker<Relay, Target>>::spawn_batch_message_worker(relay, config)
    }
}
