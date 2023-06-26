use ibc_relayer_components::chain::traits::types::chain::HasChainTypes;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::relay::traits::types::HasRelayChains;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::batch::types::aliases::MessageBatchSender;
use crate::runtime::traits::channel::HasChannelTypes;
use crate::runtime::traits::channel_once::HasChannelOnceTypes;

pub trait HasMessageBatchSender<Target>: HasRelayChains
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
    Relay: HasRelayChains,
    Relay::SrcChain:
        HasMessageBatchSenderType<Relay::Error, MessageBatchSender = SrcMessageBatchSender>,
    Relay::DstChain:
        HasMessageBatchSenderType<Relay::Error, MessageBatchSender = DstMessageBatchSender>,
{
    type SrcMessageBatchSender = SrcMessageBatchSender;

    type DstMessageBatchSender = DstMessageBatchSender;
}
