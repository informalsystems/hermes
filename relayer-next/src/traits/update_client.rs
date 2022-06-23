use async_trait::async_trait;

use super::chain_context::Height;
use super::relay_context::RelayContext;
use crate::types::message::Message;

#[async_trait]
pub trait UpdateClientMessageBuilder: RelayContext {
    async fn build_update_client_message(
        &self,
        height: Height<Self::SrcChain>,
    ) -> Result<Message<Self::DstChain, Self::SrcChain>, Self::Error>;
}
