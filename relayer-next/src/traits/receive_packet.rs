use async_trait::async_trait;

use super::chain_context::{ChannelId, Height, IbcMessage, PortId, Sequence};
use super::relay_context::RelayContext;

#[async_trait]
pub trait ReceivePacketMessageBuilder: RelayContext {
    async fn build_receive_packet_message(
        &self,
        height: Height<Self::SrcChain>,
        port_id: PortId<Self::SrcChain, Self::DstChain>,
        channel_id: ChannelId<Self::SrcChain, Self::DstChain>,
        sequence: Sequence<Self::SrcChain, Self::DstChain>,
    ) -> Result<IbcMessage<Self::DstChain, Self::SrcChain>, Self::Error>;
}
