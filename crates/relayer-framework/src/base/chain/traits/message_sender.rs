use async_trait::async_trait;

use crate::base::chain::traits::types::HasChainTypes;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasMessageSender: HasChainTypes {
    type MessageSender: MessageSender<Self>;
}

#[async_trait]
pub trait MessageSender<Chain>: Async
where
    Chain: HasChainTypes,
{
    async fn send_messages(
        chain: &Chain,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error>;
}
