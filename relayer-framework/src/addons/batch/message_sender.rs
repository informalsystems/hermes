use async_trait::async_trait;

use super::context::{BatchContext, HasBatchContext};
use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::ibc_message_sender::IbcMessageSender;
use crate::core::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct SendMessagetoBatchWorker;

pub trait HasIbcMessageSenderForBatchWorker<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<Self, Target>;
}

#[async_trait]
impl<Relay, Target, TargetChain> IbcMessageSender<Relay, Target> for SendMessagetoBatchWorker
where
    Relay: RelayContext,
    Relay: HasBatchContext<Target>,
    Relay: HasIbcMessageSenderForBatchWorker<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<Target::CounterpartyChain>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::IbcMessage>,
    ) -> Result<Vec<Vec<TargetChain::IbcEvent>>, Relay::Error> {
        let (result_sender, result_receiver) = Relay::BatchContext::new_result_channel();

        let message_sender = context.batch_channel().sender();

        Relay::BatchContext::send_batch(message_sender, messages, result_sender).await?;

        let events = Relay::BatchContext::receive_result(result_receiver).await??;

        Ok(events)
    }
}
