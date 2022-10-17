use async_trait::async_trait;

use super::context::{BatchContext, HasBatchContext};
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct SendMessagetoBatchWorker;

pub trait HasIbcMessageSenderForBatchWorker<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<Self, Target>;
}

#[async_trait]
impl<Relay, Target, TargetChain> IbcMessageSender<Relay, Target> for SendMessagetoBatchWorker
where
    Relay: HasRelayTypes,
    Relay: HasBatchContext<Target>,
    Relay: HasIbcMessageSenderForBatchWorker<Target>,
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
