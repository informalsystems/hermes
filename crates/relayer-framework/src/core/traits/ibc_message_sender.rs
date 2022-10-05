use async_trait::async_trait;

use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::traits::target::ChainTarget;
use crate::core::types::aliases::{Event, Message};
use crate::std_prelude::*;

#[async_trait]
pub trait HasIbcMessageSender<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type IbcMessageSender: IbcMessageSender<Self, Target>;
}

#[async_trait]
pub trait IbcMessageSender<Context, Target>: Async
where
    Context: RelayContext,
    Target: ChainTarget<Context>,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Context::Error>;
}

pub struct MismatchIbcEventsCountError {
    pub expected: usize,
    pub actual: usize,
}

#[async_trait]
pub trait IbcMessageSenderExt<Context, Target>
where
    Context: RelayContext,
    Target: ChainTarget<Context>,
{
    async fn send_messages(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Context::Error>;

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [Message<Target::TargetChain>; COUNT],
    ) -> Result<[Vec<Event<Target::TargetChain>>; COUNT], Context::Error>
    where
        Context::Error: From<MismatchIbcEventsCountError>;

    async fn send_message(
        &self,
        message: Message<Target::TargetChain>,
    ) -> Result<Vec<Event<Target::TargetChain>>, Context::Error>;
}

#[async_trait]
impl<Context, Target, TargetChain, Event, Message> IbcMessageSenderExt<Context, Target> for Context
where
    Context: HasIbcMessageSender<Target>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<Target::CounterpartyChain, Event = Event, Message = Message>,
    Message: Async,
{
    async fn send_messages(
        &self,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        Context::IbcMessageSender::send_messages(self, messages).await
    }

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [Message; COUNT],
    ) -> Result<[Vec<Event>; COUNT], Context::Error>
    where
        Context::Error: From<MismatchIbcEventsCountError>,
    {
        let events = self
            .send_messages(messages.into())
            .await?
            .try_into()
            .map_err(|e: Vec<_>| MismatchIbcEventsCountError {
                expected: COUNT,
                actual: e.len(),
            })?;

        Ok(events)
    }

    async fn send_message(&self, message: Message) -> Result<Vec<Event>, Context::Error> {
        let events = self
            .send_messages(vec![message])
            .await?
            .into_iter()
            .flatten()
            .collect();

        Ok(events)
    }
}
