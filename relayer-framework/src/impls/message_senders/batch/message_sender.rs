use async_trait::async_trait;

use super::context::{BatchContext, HasBatchContext};
use crate::std_prelude::*;
use crate::traits::contexts::chain::IbcChainContext;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::target::ChainTarget;

pub struct BatchedMessageSender<InSender> {
    pub sender: InSender,
}

#[async_trait]
impl<InSender, Relay, Target, TargetChain> IbcMessageSender<Relay, Target>
    for BatchedMessageSender<InSender>
where
    Relay: RelayContext,
    Relay: HasBatchContext<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    InSender: IbcMessageSender<Relay, Target>,
    TargetChain: IbcChainContext<Target::CounterpartyChain>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::IbcMessage>,
    ) -> Result<Vec<Vec<TargetChain::IbcEvent>>, Relay::Error> {
        let (result_sender, result_receiver) = context.batch_context().new_result_channel();

        let message_sender = context.messages_sender();

        Relay::BatchContext::send_messages(message_sender, messages, result_sender).await?;

        let events = Relay::BatchContext::receive_result(result_receiver).await??;

        Ok(events)
    }
}
