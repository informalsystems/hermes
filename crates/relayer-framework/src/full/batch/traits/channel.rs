use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::HasChannelTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::types::aliases::{MessageBatchReceiver, MessageBatchSender};

pub trait HasMessageBatchSender<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self, Target>;
}

pub trait HasMessageBatchReceiver<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes,
{
    fn get_batch_receiver(&self) -> &MessageBatchReceiver<Self, Target>;
}
