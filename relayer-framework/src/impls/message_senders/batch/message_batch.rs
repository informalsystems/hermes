use core::marker::PhantomData;

use crate::std_prelude::*;
use crate::traits::core::Async;
use crate::traits::message_channel::OnceChannelContext;
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

use super::message_result_channel::MessageResultChannel;

pub trait MessageBatch<Relay, Target>: Async
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    type Channel: MessageResultChannel<Relay, Target>;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (
        Self,
        <Self::Channel as MessageResultChannel<Relay, Target>>::Receiver,
    );

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>;

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        <Self::Channel as MessageResultChannel<Relay, Target>>::Sender,
    );
}

impl<Relay, Target, Channel> MessageBatch<Relay, Target>
    for (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Channel::Sender,
        PhantomData<Channel>,
    )
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
    Channel: OnceChannelContext<
        Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>,
    >,
    Relay::Error: From<Channel::Error>,
{
    type Channel = Channel;

    fn new(
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> (Self, Channel::Receiver) {
        let (sender, receiver) = Channel::new_channel();
        ((messages, sender, PhantomData), receiver)
    }

    fn messages(&self) -> &Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>> {
        &self.0
    }

    fn extract(
        self,
    ) -> (
        Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
        Channel::Sender,
    ) {
        (self.0, self.1)
    }
}
