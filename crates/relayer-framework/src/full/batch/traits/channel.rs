use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::types::aliases::{MessageBatchReceiver, MessageBatchSender};
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;

pub trait HasMessageBatchSender<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Target::TargetChain, Self::Error>;
}

pub trait HasMessageBatchReceiver<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasMutex + HasChannelTypes + HasChannelOnceTypes,
{
    fn get_batch_receiver(&self) -> &MessageBatchReceiver<Target::TargetChain, Self::Error>;
}
