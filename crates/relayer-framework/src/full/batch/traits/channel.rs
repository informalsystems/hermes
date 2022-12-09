use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::HasChannelTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::types::aliases::{MessageBatchReceiver, MessageBatchSender};

pub trait HasBatchSender<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self, Target>;
}

pub trait HasBatchReceiver<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes,
{
    fn get_batch_sender(&self) -> &MessageBatchReceiver<Self, Target>;
}
