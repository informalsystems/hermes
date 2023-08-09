use async_trait::async_trait;

use crate::chain::traits::message_sender::InjectMismatchIbcEventsCountError;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::types::aliases::{Event, Message};
use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct MainSink;

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
    Relay: HasRelayChains + HasComponents,
    Target: ChainTarget<Relay>,
    Relay::Components: IbcMessageSender<Relay, Sink, Target>,
{
    async fn send_messages(
        &self,
        _target: Target,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error> {
        Relay::Components::send_messages(self, messages).await
    }
}

#[macro_export]
macro_rules! derive_ibc_message_sender {
    ( $sink:ty, $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, Target, $( $( $param ),* )*>
            $crate::relay::traits::ibc_message_sender::IbcMessageSender<Relay, $sink, Target>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::chains::HasRelayChains,
            Target: $crate::relay::traits::target::ChainTarget<Relay>,
            $source: $crate::relay::traits::ibc_message_sender::IbcMessageSender<Relay, $sink, Target>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn send_messages(
                relay: &Relay,
                messages: Vec<<Target::TargetChain as $crate::chain::traits::types::message::HasMessageType>::Message>,
            ) -> Result<Vec<Vec<<Target::TargetChain as $crate::chain::traits::types::event::HasEventType>::Event>>, Relay::Error> {
                <$source as $crate::relay::traits::ibc_message_sender::IbcMessageSender<Relay, $sink, Target>>
                    ::send_messages(relay, messages).await
            }
        }

    };
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
