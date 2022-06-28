use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: RelayContext> {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<IbcMessage<Relay::DstChain, Relay::SrcChain>, Relay::Error>;
}

#[async_trait]
pub trait ReceivePacketRelayer<Context: RelayContext> {
    async fn relay_recv_packet(
        &self,
        context: &Context,
        height: &Height<Context::DstChain>,
        packet: Context::Packet,
    ) -> Result<(), Context::Error>;
}
