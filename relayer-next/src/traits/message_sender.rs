use async_trait::async_trait;

use crate::traits::relay_types::RelayTypes;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{IbcEvent, IbcMessage};

#[async_trait]
pub trait IbcMessageSender<Relay, Target>
where
    Relay: RelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn send_message(
        &self,
        message: IbcMessage<Target::TargetChain, Target::CounterpartyChain>,
    ) -> Result<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>, Relay::Error>;

    async fn send_messages(
        &self,
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Relay::Error>;

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [IbcMessage<Target::TargetChain, Target::CounterpartyChain>; COUNT],
    ) -> Result<[Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>; COUNT], Relay::Error>;
}
