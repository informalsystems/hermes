use async_trait::async_trait;

use crate::traits::relay_types::RelayTypes;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait UpdateClientMessageBuilder<Relay: RelayTypes> {
    async fn build_update_client_messages(
        &self,
        height: Height<Relay::SrcChain>,
    ) -> Result<Vec<IbcMessage<Relay::DstChain, Relay::SrcChain>>, Relay::Error>;
}
