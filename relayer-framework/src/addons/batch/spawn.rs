use core::marker::PhantomData;

use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::runtime::log::{HasLogger, LevelDebug};
use crate::core::traits::runtime::sleep::CanSleep;
use crate::core::traits::runtime::spawn::HasSpawner;
use crate::core::traits::runtime::time::HasTime;
use crate::core::traits::target::ChainTarget;
use crate::std_prelude::*;

use super::config::BatchConfig;
use super::context::HasBatchContext;
use super::message_sender::HasIbcMessageSenderForBatchWorker;
use super::worker::BatchMessageWorker;

pub struct BatchMessageWorkerSpawner<Target>(PhantomData<Target>);

pub trait CanSpawnBatchMessageWorker<Relay, Target>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Relay: HasBatchContext<Target>,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig);
}

impl<Relay, Target, TargetChain, Runtime> CanSpawnBatchMessageWorker<Relay, Target>
    for BatchMessageWorkerSpawner<Target>
where
    Relay: RelayContext<Runtime = Runtime>,
    Relay: HasIbcMessageSenderForBatchWorker<Target>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Relay: HasBatchContext<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<Target::CounterpartyChain>,
    Relay::Error: Clone,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        <BatchMessageWorker<Relay, Target, Relay::IbcMessageSenderForBatchWorker>>::spawn_batch_message_worker(
            relay,
            config,
        )
    }
}
