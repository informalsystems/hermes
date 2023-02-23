use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::types::aliases::{Event, Message};
use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanSendIbcMessages<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
{
    async fn send_messages(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error>;
}

#[async_trait]
pub trait IbcMessageSender<Context, Target>: Async
where
    Context: HasRelayTypes,
    Target: ChainTarget<Context>,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Context::Error>;
}

pub trait InjectMismatchIbcEventsCountError: HasErrorType {
    fn mismatch_ibc_events_count_error(expected: usize, actual: usize) -> Self::Error;
}

#[async_trait]
pub trait IbcMessageSenderExt<Context, Target>
where
    Context: HasRelayTypes,
    Target: ChainTarget<Context>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [Message<Target::TargetChain>; COUNT],
    ) -> Result<[Vec<Event<Target::TargetChain>>; COUNT], Context::Error>
    where
        Context: InjectMismatchIbcEventsCountError;

    async fn send_message(
        &self,
        message: Message<Target::TargetChain>,
    ) -> Result<Vec<Event<Target::TargetChain>>, Context::Error>;
}

#[async_trait]
impl<Context, Target, TargetChain, Event, Message> IbcMessageSenderExt<Context, Target> for Context
where
    Context: CanSendIbcMessages<Target>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain, Event = Event, Message = Message>,
    Message: Async,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [Message; COUNT],
    ) -> Result<[Vec<Event>; COUNT], Context::Error>
    where
        Context: InjectMismatchIbcEventsCountError,
    {
        let events = self
            .send_messages(messages.into())
            .await?
            .try_into()
            .map_err(|e: Vec<_>| Context::mismatch_ibc_events_count_error(COUNT, e.len()))?;

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
