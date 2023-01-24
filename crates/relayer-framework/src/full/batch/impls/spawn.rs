use core::marker::PhantomData;

use crate::base::chain::traits::types::{CanEstimateMessageSize, HasIbcChainTypes};
use crate::base::core::traits::error::CanShareError;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::log::{HasLogger, LevelDebug};
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::base::runtime::traits::time::HasTime;
use crate::full::batch::traits::channel::HasMessageBatchReceiver;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::batch::traits::spawn::CanSpawnBatchMessageWorker;
use crate::full::batch::types::config::BatchConfig;
use crate::full::batch::worker::BatchMessageWorker;
use crate::full::runtime::traits::channel::CanUseChannels;
use crate::full::runtime::traits::channel_once::CanUseChannelsOnce;
use crate::full::runtime::traits::spawn::HasSpawner;

pub struct BatchMessageWorkerSpawner<Target>(PhantomData<Target>);

impl<Relay, Target, TargetChain, Runtime> CanSpawnBatchMessageWorker<Relay, Target>
    for BatchMessageWorkerSpawner<Target>
where
    Relay: HasRelayTypes,
    Relay: HasRuntime<Runtime = Runtime>,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Relay: HasMessageBatchReceiver<Target>,
    Relay: CanShareError,
    TargetChain: CanEstimateMessageSize,
    TargetChain: HasRuntime<Runtime = Runtime>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    Runtime: HasTime + CanSleep + HasSpawner + HasLogger<LevelDebug>,
    Runtime: HasMutex + CanUseChannelsOnce + CanUseChannels,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig) {
        <BatchMessageWorker<Relay, Target>>::spawn_batch_message_worker(relay, config)
    }
}
