use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::ChainTarget;
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

pub trait HasMessageBatchSenderType<Error>: Async {
    type MessageBatchSender: Async;
}

impl<Chain, Error> HasMessageBatchSenderType<Error> for Chain
where
    Error: Async,
    Chain: HasChainTypes + HasRuntime,
    Chain::Runtime: HasChannelTypes + HasChannelOnceTypes,
{
    type MessageBatchSender = MessageBatchSender<Chain, Error>;
}

pub trait HasMessageBatchSenderTypes: Async {
    type SrcMessageBatchSender: Async;

    type DstMessageBatchSender: Async;
}

impl<Relay, SrcMessageBatchSender, DstMessageBatchSender> HasMessageBatchSenderTypes for Relay
where
    SrcMessageBatchSender: Async,
    DstMessageBatchSender: Async,
    Relay: HasRelayTypes,
    Relay::SrcChain:
        HasMessageBatchSenderType<Relay::Error, MessageBatchSender = SrcMessageBatchSender>,
    Relay::DstChain:
        HasMessageBatchSenderType<Relay::Error, MessageBatchSender = DstMessageBatchSender>,
{
    type SrcMessageBatchSender = SrcMessageBatchSender;

    type DstMessageBatchSender = DstMessageBatchSender;
}
