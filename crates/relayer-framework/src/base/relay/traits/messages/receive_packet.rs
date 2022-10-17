use async_trait::async_trait;

use crate::base::chain::types::aliases::{Height, Message};
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildReceivePacketMessage: HasRelayTypes {
    async fn build_receive_packet_message(
        &self,
        height: &Height<Self::SrcChain>,
        packet: &Self::Packet,
    ) -> Result<Message<Self::DstChain>, Self::Error>;
}

#[async_trait]
pub trait ReceivePacketMessageBuilder<Relay: HasRelayTypes> {
    async fn build_receive_packet_message(
        relay: &Relay,
        height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Message<Relay::DstChain>, Relay::Error>;
}
