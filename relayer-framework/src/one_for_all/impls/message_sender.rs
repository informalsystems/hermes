use async_trait::async_trait;

use crate::core::traits::message_sender::{HasMessageSender, MessageSender};
use crate::one_for_all::impls::message::OfaMessage;
use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext};
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::std_prelude::*;

pub struct OfaMessageSender;

impl<Chain: OfaChain> HasMessageSender for OfaChainContext<Chain> {
    type MessageSender = OfaMessageSender;
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
