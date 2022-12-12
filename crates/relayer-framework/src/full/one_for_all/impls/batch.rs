use async_trait::async_trait;

use crate::base::chain::types::aliases::{Event, Message};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::full::batch::message_sender::CanSendIbcMessagesFromBatchWorker;
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
