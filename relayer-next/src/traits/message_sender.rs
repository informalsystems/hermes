use async_trait::async_trait;
use ibc::events::IbcEvent;

use super::context::RelayContext;
use crate::tagged::DualTagged;
use crate::types::message::Message;

#[async_trait]
pub trait MessageSender: RelayContext {
    async fn send_message(
        &self,
        message: Message<Self::DstChain, Self::SrcChain>,
    ) -> Result<DualTagged<Self::DstChain, Self::SrcChain, Vec<IbcEvent>>, Self::Error>;

    async fn send_messages(
        &self,
        messages: Vec<Message<Self::DstChain, Self::SrcChain>>,
    ) -> Result<DualTagged<Self::DstChain, Self::SrcChain, Vec<IbcEvent>>, Self::Error>;
}
