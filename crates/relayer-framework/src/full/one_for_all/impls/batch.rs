use async_trait::async_trait;

use crate::base::chain::types::aliases::{Event, Message};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::full::batch::message_sender::CanSendIbcMessagesFromBatchWorker;
use crate::full::batch::traits::channel::{HasMessageBatchReceiver, HasMessageBatchSender};
use crate::full::batch::types::aliases::{MessageBatchReceiver, MessageBatchSender};
use crate::full::one_for_all::traits::relay::OfaFullRelay;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Target> CanSendIbcMessagesFromBatchWorker<Target> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    Target: ChainTarget<Self>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>: IbcMessageSender<Self, Target>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error> {
        <SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>>::send_messages(self, messages)
            .await
    }
}

impl<Relay> HasMessageBatchSender<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error> {
        self.relay.src_chain_message_batch_sender()
    }
}

impl<Relay> HasMessageBatchReceiver<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_receiver(&self) -> &MessageBatchReceiver<Self::SrcChain, Self::Error> {
        self.relay.src_chain_message_batch_receiver()
    }
}

impl<Relay> HasMessageBatchSender<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error> {
        self.relay.dst_chain_message_batch_sender()
    }
}

impl<Relay> HasMessageBatchReceiver<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_receiver(&self) -> &MessageBatchReceiver<Self::DstChain, Self::Error> {
        self.relay.dst_chain_message_batch_receiver()
    }
}
