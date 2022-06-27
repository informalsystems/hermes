use async_trait::async_trait;

use crate::traits::core::CoreTraits;
use crate::traits::relay_types::RelayTypes;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSender<Relay, Target>: CoreTraits
where
    Relay: RelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn send_messages(
        &self,
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>;
}

pub struct MismatchIbcEventsCountError {
    pub expected: usize,
    pub actual: usize,
}

#[async_trait]
pub trait IbcMessageSenderExt<Relay, Target>: IbcMessageSender<Relay, Target>
where
    Relay: RelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<[Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT], Relay::Error>
    where
        Relay::Error: From<MismatchIbcEventsCountError>;

    async fn send_message(
        &self,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Context, Relay, Target> IbcMessageSenderExt<Relay, Target> for Context
where
    Context: IbcMessageSender<Relay, Target>,
    Relay: RelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<[Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT], Relay::Error>
    where
        Relay::Error: From<MismatchIbcEventsCountError>,
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

    async fn send_message(
        &self,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<(), Relay::Error> {
        self.send_messages(vec![message]).await?;

        Ok(())
    }
}
