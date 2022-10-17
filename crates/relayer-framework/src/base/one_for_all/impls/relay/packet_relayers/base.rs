use async_trait::async_trait;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayComponents;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::packet_relayer::{CanRelayPacket, PacketRelayer};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Components> CanRelayPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Components::PacketRelayer::relay_packet(self, packet).await
    }
}
