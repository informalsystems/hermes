use async_trait::async_trait;

use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait CanSendMessages: HasMessageType + HasEventType {
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;
}

#[async_trait]
pub trait MessageSender<Chain>: Async
where
    Chain: HasMessageType + HasEventType,
{
    async fn send_messages(
        chain: &Chain,
        messages: Vec<Chain::Message>,
    ) -> Result<Vec<Vec<Chain::Event>>, Chain::Error>;
}
