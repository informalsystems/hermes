use async_trait::async_trait;

use crate::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::impls::one_for_all::chain::OfaChainContext;
use crate::impls::one_for_all::error::OfaErrorContext;
use crate::impls::one_for_all::message::OfaMessage;
use crate::impls::one_for_all::relay::OfaRelayContext;
use crate::std_prelude::*;
use crate::traits::ibc_message_sender::IbcMessageSenderContext;
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
use crate::traits::one_for_all::chain::OfaChain;
use crate::traits::one_for_all::relay::OfaRelay;
use crate::traits::target::{DestinationTarget, SourceTarget};

pub struct OfaMessageSender;

impl<Chain: OfaChain> MessageSenderContext for OfaChainContext<Chain> {
    type MessageSender = OfaMessageSender;
}

impl<Relay: OfaRelay> IbcMessageSenderContext<SourceTarget> for OfaRelayContext<Relay> {
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}

impl<Relay: OfaRelay> IbcMessageSenderContext<DestinationTarget> for OfaRelayContext<Relay> {
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}

#[async_trait]
impl<Chain: OfaChain> MessageSender<OfaChainContext<Chain>> for OfaMessageSender {
    async fn send_messages(
        context: &OfaChainContext<Chain>,
        messages: Vec<OfaMessage<Chain>>,
    ) -> Result<Vec<Vec<Chain::Event>>, OfaErrorContext<Chain::Error>> {
        let in_messages = messages.into_iter().map(|m| m.message).collect();

        let events = context.chain.send_messages(in_messages).await?;

        Ok(events)
    }
}
