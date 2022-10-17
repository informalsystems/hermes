use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn relay_packet(context: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayPacket: HasRelayTypes {
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error>;
}
