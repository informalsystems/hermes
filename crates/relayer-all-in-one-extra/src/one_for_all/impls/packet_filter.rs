use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_components::relay::traits::packet_filter::PacketFilter;

use crate::one_for_all::traits::relay::OfaFullRelay;
use crate::std_prelude::*;

pub struct FilterPacketFromOfa;

#[async_trait]
impl<Relay> PacketFilter<OfaRelayWrapper<Relay>> for FilterPacketFromOfa
where
    Relay: OfaFullRelay,
{
    async fn should_relay_packet(
        relay: &OfaRelayWrapper<Relay>,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        relay.relay.should_relay_packet(packet).await
    }
}
