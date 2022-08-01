use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::message_channel::{HasChannelContext, OnceChannelContext};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

use super::message_result_channel::{MessageResultReceiver, MessageResultSender};

pub trait MessageBatch<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type ResultSender: MessageResultSender<Relay, Target>;
    type ResultReceiver: MessageResultReceiver<Relay, Target>;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (Self, Self::ResultReceiver);

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>;

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Self::ResultSender,
    );
}

impl<Relay, Target, Channel, Sender, Receiver> MessageBatch<Relay, Target>
    for (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Sender,
    )
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Sender: Async,
    Receiver: Async,
    Relay: HasChannelContext<ChannelContext = Channel>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
        Sender = Sender,
        Receiver = Receiver,
    >,
    Relay::Error: From<Channel::Error>,
{
    type ResultSender = Sender;
    type ResultReceiver = Receiver;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (Self, Self::ResultReceiver) {
        let (sender, receiver) = Channel::new_channel();
        ((messages, sender), receiver)
    }

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>> {
        &self.0
    }

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Self::ResultSender,
    ) {
        (self.0, self.1)
    }
}
