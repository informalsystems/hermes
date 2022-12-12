use async_trait::async_trait;

use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::chain::types::aliases::{Event, Message};
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::channel::{
    CanCreateChannels, CanUseChannels, CanUseChannelsOnce,
};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::traits::channel::HasMessageBatchSender;
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
impl<Relay, Target, TargetChain, Runtime> IbcMessageSender<Relay, Target>
    for SendMessagetoBatchWorker
where
    Relay: HasRelayTypes,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanCreateChannels + CanUseChannels + CanUseChannelsOnce,
    Relay: HasMessageBatchSender<Target>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::Message>,
    ) -> Result<Vec<Vec<TargetChain::Event>>, Relay::Error> {
        let (result_sender, result_receiver) = Runtime::new_channel();

        let message_sender = context.get_batch_sender();

        Runtime::send(message_sender, (messages, result_sender))
            .map_err(TargetChain::runtime_error)
            .map_err(Target::target_chain_error)?;

        let events = Runtime::receive_once(result_receiver)
            .await
            .map_err(TargetChain::runtime_error)
            .map_err(Target::target_chain_error)??;

        Ok(events)
    }
}
