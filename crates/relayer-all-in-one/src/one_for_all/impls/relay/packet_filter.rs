use async_trait::async_trait;
use ibc_relayer_components::relay::traits::components::packet_filter::PacketFilter;

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::component::OfaComponents;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> PacketFilter<OfaRelayWrapper<Relay>> for OfaComponents
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
