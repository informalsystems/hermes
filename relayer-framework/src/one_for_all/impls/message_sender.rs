use async_trait::async_trait;

use crate::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::error::OfaErrorContext;
use crate::one_for_all::impls::message::OfaMessage;
use crate::one_for_all::impls::relay::OfaRelayContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::std_prelude::*;
use crate::traits::ibc_message_sender::IbcMessageSenderContext;
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
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
