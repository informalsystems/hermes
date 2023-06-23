use async_trait::async_trait;
use ibc_relayer_components::relay::traits::packet_relayer::{CanRelayPacket, PacketRelayer};

use crate::one_for_all::components;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        components::PacketRelayer::relay_packet(self, packet).await
    }
}
