use core::marker::PhantomData;

use async_trait::async_trait;

use crate::chain::traits::components::message_sender::InjectMismatchIbcEventsCountError;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::types::aliases::{Event, Message};
use crate::core::traits::component::DelegateComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct MainSink;

pub struct IbcMessageSenderComponent<Sink>(pub PhantomData<Sink>);

#[async_trait]
pub trait IbcMessageSender<Relay, Sink, Target>: Async
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    async fn send_messages(
        relay: &Relay,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Relay::Error>;
}

#[async_trait]
impl<Component, Relay, Sink, Target> IbcMessageSender<Relay, Sink, Target> for Component
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    Component: DelegateComponent<IbcMessageSenderComponent<Sink>>,
    Component::Delegate: IbcMessageSender<Relay, Sink, Target>,
{
    async fn send_messages(
        relay: &Relay,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Relay::Error> {
        Component::Delegate::send_messages(relay, messages).await
    }
}

#[async_trait]
pub trait CanSendIbcMessages<Sink, Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn send_messages(
        &self,
        target: Target,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error>;
}

#[async_trait]
impl<Relay, Sink, Target> CanSendIbcMessages<Sink, Target> for Relay
where
    Relay: HasRelayChains + DelegateComponent<IbcMessageSenderComponent<Sink>>,
    Target: ChainTarget<Relay>,
    Relay::Delegate: IbcMessageSender<Relay, Sink, Target>,
{
    async fn send_messages(
        &self,
        _target: Target,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error> {
        Relay::Delegate::send_messages(self, messages).await
    }
}

#[async_trait]
pub trait CanSendFixSizedIbcMessages<Sink, Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        target: Target,
        messages: [Message<Target::TargetChain>; COUNT],
    ) -> Result<[Vec<Event<Target::TargetChain>>; COUNT], Self::Error>;
}

#[async_trait]
pub trait CanSendSingleIbcMessage<Sink, Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn send_message(
        &self,
        target: Target,
        message: Message<Target::TargetChain>,
    ) -> Result<Vec<Event<Target::TargetChain>>, Self::Error>;
}

#[async_trait]
impl<Relay, Sink, Target, TargetChain, Event, Message> CanSendFixSizedIbcMessages<Sink, Target>
    for Relay
where
    Relay: CanSendIbcMessages<Sink, Target> + InjectMismatchIbcEventsCountError,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain, Event = Event, Message = Message>,
    Message: Async,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        target: Target,
        messages: [Message; COUNT],
    ) -> Result<[Vec<Event>; COUNT], Relay::Error> {
        let events_vec = self.send_messages(target, messages.into()).await?;

        let events = events_vec
            .try_into()
            .map_err(|e: Vec<_>| Relay::mismatch_ibc_events_count_error(COUNT, e.len()))?;

        Ok(events)
    }
}

#[async_trait]
impl<Relay, Sink, Target, TargetChain, Event, Message> CanSendSingleIbcMessage<Sink, Target>
    for Relay
where
    Relay: CanSendIbcMessages<Sink, Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain, Event = Event, Message = Message>,
    Message: Async,
{
    async fn send_message(
        &self,
        target: Target,
        message: Message,
    ) -> Result<Vec<Event>, Relay::Error> {
        let events = self
            .send_messages(target, vec![message])
            .await?
            .into_iter()
            .flatten()
            .collect();

        Ok(events)
    }
}
