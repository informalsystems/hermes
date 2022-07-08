use async_trait::async_trait;

use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSenderContext<Target>: RelayContext
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
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Context::Error>;
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
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Context::Error>;

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<
        [Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT],
        Context::Error,
    >
    where
        Context::Error: From<MismatchIbcEventsCountError>;

    async fn send_message(
        &self,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>, Context::Error>;
}

#[async_trait]
impl<Context, Target, TargetChain, Event, Message> IbcMessageSenderExt<Context, Target> for Context
where
    Context: IbcMessageSenderContext<Target>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<Target::CounterpartyChain, IbcEvent = Event, IbcMessage = Message>,
    Message: Async,
{
    async fn send_messages(
        &self,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        Context::IbcMessageSender::send_messages(&self, messages).await
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
