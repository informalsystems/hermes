use async_trait::async_trait;

use crate::core::traits::contexts::filter::PacketFilter;
use crate::core::traits::contexts::relay::RelayContext;
use crate::std_prelude::*;

pub struct PacketAccountFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for PacketAccountFilter
where Relay: RelayContext {
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}