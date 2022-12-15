use core::marker::PhantomData;

use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::CanUseChannels;
use crate::base::runtime::traits::channel_once::CanUseChannelsOnce;
use crate::base::runtime::traits::log::{HasLogger, LevelDebug};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::spawn::HasSpawner;
use crate::base::runtime::traits::time::HasTime;
use crate::full::batch::traits::channel::HasMessageBatchReceiver;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::batch::traits::spawn::CanSpawnBatchMessageWorker;
use crate::full::batch::types::config::BatchConfig;
use crate::full::batch::worker::BatchMessageWorker;
use crate::std_prelude::*;

pub struct BatchMessageWorkerSpawner<Target>(PhantomData<Target>);

impl<Relay, Target, TargetChain, Runtime> CanSpawnBatchMessageWorker<Relay, Target>
    for BatchMessageWorkerSpawner<Target>
where
    Relay: HasRelayTypes,
    Relay: HasRuntime<Runtime = Runtime>,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Runtime: CanUseChannelsOnce + CanUseChannels,
    Relay: HasMessageBatchReceiver<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    Relay::Error: Clone,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        <BatchMessageWorker<Relay, Target>>::spawn_batch_message_worker(relay, config)
    }
}
