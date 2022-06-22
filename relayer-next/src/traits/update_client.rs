use async_trait::async_trait;
use ibc::Height;

use super::context::RelayContext;
use crate::tagged::MonoTagged;
use crate::types::message::Message;

#[async_trait]
pub trait UpdateClientMessageBuilder: RelayContext {
    async fn build_update_client_message(
        &self,
        height: MonoTagged<Self::SrcChain, Height>,
    ) -> Result<Message<Self::DstChain, Self::SrcChain>, Self::Error>;
}
