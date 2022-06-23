use async_trait::async_trait;

use super::relay_context::RelayContext;
use crate::traits::chain_context::{ChannelId, Height, IbcMessage, PortId, Sequence};

#[async_trait]
pub trait AckPacketMessageBuilder: RelayContext {
    async fn build_ack_packet_message(
        &self,
        height: Height<Self::DstChain>,
        port_id: PortId<Self::DstChain, Self::SrcChain>,
        channel_id: ChannelId<Self::DstChain, Self::SrcChain>,
        sequence: Sequence<Self::SrcChain, Self::DstChain>,
    ) -> Result<IbcMessage<Self::SrcChain, Self::DstChain>, Self::Error>;
}
