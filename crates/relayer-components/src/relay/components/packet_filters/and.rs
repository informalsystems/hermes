use core::marker::PhantomData;

use async_trait::async_trait;

use crate::relay::traits::components::packet_filter::PacketFilter;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct And<FilterA, FilterB>(pub PhantomData<(FilterA, FilterB)>);

#[async_trait]
impl<Relay, FilterA, FilterB> PacketFilter<Relay> for And<FilterA, FilterB>
where
    Relay: HasRelayPacket,
    FilterA: PacketFilter<Relay>,
    FilterB: PacketFilter<Relay>,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        if FilterA::should_relay_packet(relay, packet).await? {
            FilterB::should_relay_packet(relay, packet).await
        } else {
            Ok(false)
        }
    }
}
