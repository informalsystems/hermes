use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainWrapper};
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::traits::message_sender::{HasMessageSender, MessageSender};
use crate::std_prelude::*;

pub struct OfaMessageSender;

impl<Chain: OfaChain> HasMessageSender for OfaChainWrapper<Chain> {
    type MessageSender = OfaMessageSender;
}

#[async_trait]
impl<Chain: OfaChain> MessageSender<OfaChainWrapper<Chain>> for OfaMessageSender {
    async fn send_messages(
        context: &OfaChainWrapper<Chain>,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, OfaErrorContext<Chain::Error>> {
        let events = context.chain.send_messages(messages).await?;

        Ok(events)
    }
}
