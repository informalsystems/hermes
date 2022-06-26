use async_trait::async_trait;

use crate::traits::relay_types::RelayTypes;
use crate::types::aliases::{ChannelId, Height, IbcMessage, PortId, Sequence};

#[async_trait]
pub trait AckPacketMessageBuilder<Relay: RelayTypes> {
    async fn build_ack_packet_message(
        &self,
        height: Height<Relay::DstChain>,
        port_id: PortId<Relay::DstChain, Relay::SrcChain>,
        channel_id: ChannelId<Relay::DstChain, Relay::SrcChain>,
        sequence: Sequence<Relay::SrcChain, Relay::DstChain>,
    ) -> Result<IbcMessage<Relay::SrcChain, Relay::DstChain>, Relay::Error>;
}
