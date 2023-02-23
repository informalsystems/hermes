use async_trait::async_trait;
use ibc_relayer_components::relay::impls::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::{
    AckPacketRelayer, CanRelayAckPacket,
};

use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaBaseRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayAckPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    BaseAckPacketRelayer: AckPacketRelayer<Self>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Self::Packet,
        ack: &<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<(), Relay::Error> {
        BaseAckPacketRelayer::relay_ack_packet(self, destination_height, packet, ack).await
    }
}
