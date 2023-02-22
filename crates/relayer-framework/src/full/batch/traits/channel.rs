use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::{ChainTarget, DestinationTarget, SourceTarget};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::types::aliases::MessageBatchSender;
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

pub trait HasMessageBatchSenderType<Target>: Async {
    type MessageBatchSender: Async;
}

impl<Relay, Target> HasMessageBatchSenderType<Target> for Relay
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasRuntime,
    <Target::TargetChain as HasRuntime>::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    type MessageBatchSender = MessageBatchSender<Target::TargetChain, Relay::Error>;
}

pub trait HasMessageBatchSenderTypes: Async {
    type SrcMessageBatchSender: Async;

    type DstMessageBatchSender: Async;
}

impl<Relay, SrcMessageBatchSender, DstMessageBatchSender> HasMessageBatchSenderTypes for Relay
where
    SrcMessageBatchSender: Async,
    DstMessageBatchSender: Async,
    Relay: HasRelayTypes
        + HasMessageBatchSenderType<SourceTarget, MessageBatchSender = SrcMessageBatchSender>
        + HasMessageBatchSenderType<DestinationTarget, MessageBatchSender = DstMessageBatchSender>,
{
    type SrcMessageBatchSender = SrcMessageBatchSender;

    type DstMessageBatchSender = DstMessageBatchSender;
}
