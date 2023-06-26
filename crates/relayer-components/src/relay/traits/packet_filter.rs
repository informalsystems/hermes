use async_trait::async_trait;

use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

#[async_trait]
pub trait CanFilterPackets: HasRelayPacket {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;
}
