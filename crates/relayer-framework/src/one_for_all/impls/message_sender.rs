use async_trait::async_trait;

use crate::core::traits::message_sender::{HasMessageSender, MessageSender};
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
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, OfaErrorContext<Chain::Error>> {
        let events = context.chain.send_messages(messages).await?;

        Ok(events)
    }
}
