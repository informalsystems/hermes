use async_trait::async_trait;

use super::context::{BatchContext, HasBatchContext};
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::chain::types::aliases::{Event, Message};
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct SendMessagetoBatchWorker;

#[async_trait]
pub trait CanSendIbcMessagesFromBatchWorker<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error>;
}

#[async_trait]
impl<Relay, Target, TargetChain> IbcMessageSender<Relay, Target> for SendMessagetoBatchWorker
where
    Relay: HasRelayTypes,
    Relay: HasBatchContext<Target>,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::Message>,
    ) -> Result<Vec<Vec<TargetChain::Event>>, Relay::Error> {
        let (result_sender, result_receiver) = Relay::BatchContext::new_result_channel();

        let message_sender = context.batch_channel().sender();

        Relay::BatchContext::send_batch(message_sender, messages, result_sender).await?;

        let events = Relay::BatchContext::receive_result(result_receiver).await??;

        Ok(events)
    }
}
