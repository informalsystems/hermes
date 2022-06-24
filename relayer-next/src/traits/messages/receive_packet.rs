use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{Height, IbcMessage, Packet};

#[async_trait]
pub trait ReceivePacketMessageBuilder: RelayContext {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Self::SrcChain>,
        packet: &Packet<Self>,
    ) -> Result<IbcMessage<Self::DstChain, Self::SrcChain>, Self::Error>;
}
