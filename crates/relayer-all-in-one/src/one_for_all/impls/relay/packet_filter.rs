use async_trait::async_trait;

use crate::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayPreset};
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::packet_filter::{CanFilterPackets, PacketFilter};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Preset> CanFilterPackets for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Preset::PacketFilter::should_relay_packet(self, packet).await
    }
}
