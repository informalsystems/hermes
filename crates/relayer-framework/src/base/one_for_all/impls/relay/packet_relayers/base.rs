use async_trait::async_trait;

use crate::base::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset};
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::packet_relayer::{CanRelayPacket, PacketRelayer};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Preset> CanRelayPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Preset::PacketRelayer::relay_packet(self, packet).await
    }
}
