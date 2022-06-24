use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait UpdateClientMessageBuilder: RelayContext {
    async fn build_update_client_messages(
        &self,
        height: Height<Self::SrcChain>,
    ) -> Result<Vec<IbcMessage<Self::DstChain, Self::SrcChain>>, Self::Error>;
}
