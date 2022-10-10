use async_trait::async_trait;

use crate::base::traits::contexts::relay::RelayContext;
use crate::base::types::aliases::{Height, Message};
use crate::std_prelude::*;

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: RelayContext> {
    async fn build_receive_packet_message(
        relay: &Relay,
        height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::DstChain>, Relay::Error>;
}

#[async_trait]
pub trait HasReceivePacketMessageBuilder: RelayContext {
    type ReceivePacketMessageBuilder: ReceivePacketMessageBuilder<Self>;

    async fn build_receive_packet_message(
        &self,
        height: &Height<Self::SrcChain>,
        packet: &Self::Packet,
    ) -> Result<Message<Self::DstChain>, Self::Error> {
        Self::ReceivePacketMessageBuilder::build_receive_packet_message(self, height, packet).await
    }
}
