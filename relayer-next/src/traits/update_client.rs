use async_trait::async_trait;

use super::relay_context::RelayContext;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait UpdateClientMessageBuilder: RelayContext {
    async fn build_update_client_message(
        &self,
        height: Height<Self::SrcChain>,
    ) -> Result<IbcMessage<Self::DstChain, Self::SrcChain>, Self::Error>;
}
