use async_trait::async_trait;

use crate::base::chain::traits::message_sender::{HasMessageSender, MessageSender};
use crate::base::one_for_all::traits::chain::OfaBaseChain;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

pub struct OfaMessageSender;

impl<Chain: OfaBaseChain> HasMessageSender for OfaChainWrapper<Chain> {
    type MessageSender = OfaMessageSender;
}

#[async_trait]
impl<Chain: OfaBaseChain> MessageSender<OfaChainWrapper<Chain>> for OfaMessageSender {
    async fn send_messages(
        context: &OfaChainWrapper<Chain>,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error> {
        let events = context.chain.send_messages(messages).await?;

        Ok(events)
    }
}
