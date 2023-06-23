use async_trait::async_trait;
use ibc_relayer_components::relay::traits::packet_filter::{CanFilterPackets, PacketFilter};

use crate::one_for_all::components;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

pub struct FilterPacketFromOfa;

#[async_trait]
impl<Relay> PacketFilter<OfaRelayWrapper<Relay>> for FilterPacketFromOfa
where
    Relay: OfaRelay,
{
    async fn should_relay_packet(
        relay: &OfaRelayWrapper<Relay>,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        relay.relay.should_relay_packet(packet).await
    }
}

#[async_trait]
impl<Relay> CanFilterPackets for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        components::PacketFilter::should_relay_packet(self, packet).await
    }
}
