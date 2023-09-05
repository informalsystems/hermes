use async_trait::async_trait;
use ibc_relayer_components::chain::traits::components::message_sender::MessageSender;

use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::one_for_all::types::component::OfaComponents;
use crate::std_prelude::*;

#[async_trait]
impl<Chain> MessageSender<OfaChainWrapper<Chain>> for OfaComponents
where
    Chain: OfaChain,
{
    async fn send_messages(
        chain: &OfaChainWrapper<Chain>,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error> {
        let events = chain.chain.send_messages(messages).await?;
        Ok(events)
    }
}
