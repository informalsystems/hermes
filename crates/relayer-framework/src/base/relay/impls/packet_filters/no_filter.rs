use async_trait::async_trait;

use crate::base::relay::traits::packet_filter::PacketFilter;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct NoPacketFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for NoPacketFilter
where
    Relay: HasRelayTypes,
{
    async fn should_relay_packet(
        _relay: &Relay,
        _packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}
