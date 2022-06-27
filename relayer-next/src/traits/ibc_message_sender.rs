use async_trait::async_trait;

use crate::traits::core::Async;
use crate::traits::relay_types::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

pub trait IbcMessageSenderContext<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type IbcMessageSender: IbcMessageSender<Self, Target>;

    fn ibc_message_sender(&self) -> &Self::IbcMessageSender;
}

#[async_trait]
pub trait IbcMessageSender<Context, Target>: Async
where
    Context: RelayContext,
    Target: ChainTarget<Context>,
{
    async fn send_messages(
        &self,
        context: &Context,
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Context::Error>;
}

pub struct MismatchIbcEventsCountError {
    pub expected: usize,
    pub actual: usize,
}

#[async_trait]
pub trait IbcMessageSenderExt<Context, Target>: IbcMessageSender<Context, Target>
where
    Context: RelayContext,
    Target: ChainTarget<Context>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        context: &Context,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<
        [Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT],
        Context::Error,
    >
    where
        Context::Error: From<MismatchIbcEventsCountError>;

    async fn send_message(
        &self,
        context: &Context,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<(), Context::Error>;
}

#[async_trait]
impl<Context, Target, Sender> IbcMessageSenderExt<Context, Target> for Sender
where
    Context: RelayContext,
    Sender: IbcMessageSender<Context, Target>,
    Target: ChainTarget<Context>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        context: &Context,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<
        [Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT],
        Context::Error,
    >
    where
        Context::Error: From<MismatchIbcEventsCountError>,
    {
        let events = self
            .send_messages(context, messages.into())
            .await?
            .try_into()
            .map_err(|e: Vec<_>| MismatchIbcEventsCountError {
                expected: COUNT,
                actual: e.len(),
            })?;

        Ok(events)
    }

    async fn send_message(
        &self,
        context: &Context,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<(), Context::Error> {
        self.send_messages(context, vec![message]).await?;

        Ok(())
    }
}
