use async_trait::async_trait;

use crate::core::traits::sync::Async;
use crate::relay::traits::types::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayPacket: HasRelayPacket {
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error>;
}
