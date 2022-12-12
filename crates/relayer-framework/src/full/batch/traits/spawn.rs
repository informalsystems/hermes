use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::full::batch::types::config::BatchConfig;

pub trait CanSpawnBatchMessageWorker<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    fn spawn_batch_message_worker(relay: Relay, config: BatchConfig);
}
