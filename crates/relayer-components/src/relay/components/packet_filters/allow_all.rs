use async_trait::async_trait;

use crate::relay::traits::components::packet_filter::PacketFilter;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct AllowAll;

#[async_trait]
impl<Relay> PacketFilter<Relay> for AllowAll
where
    Relay: HasRelayPacket,
{
    async fn should_relay_packet(
        _relay: &Relay,
        _packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}
