use async_trait::async_trait;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::{
    AckPacketRelayer, CanRelayAckPacket,
};

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayAckPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
    components::AckPacketRelayer: AckPacketRelayer<Self>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &<Relay::DstChain as OfaChain>::Height,
        packet: &Self::Packet,
        ack: &<Relay::DstChain as OfaChain>::WriteAcknowledgementEvent,
    ) -> Result<(), Relay::Error> {
        components::AckPacketRelayer::relay_ack_packet(self, destination_height, packet, ack).await
    }
}
