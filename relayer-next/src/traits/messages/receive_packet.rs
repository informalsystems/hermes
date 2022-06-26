use async_trait::async_trait;

use crate::traits::relay_types::RelayTypes;
use crate::types::aliases::{Height, IbcMessage, Packet};

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: RelayTypes> {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Relay::SrcChain>,
        packet: &Packet<Relay>,
    ) -> Result<IbcMessage<Relay::DstChain, Relay::SrcChain>, Relay::Error>;
}
