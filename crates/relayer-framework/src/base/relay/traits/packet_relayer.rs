use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::context::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn relay_packet(context: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait HasPacketRelayer: HasRelayTypes {
    type PacketRelayer: PacketRelayer<Self>;

    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Self::PacketRelayer::relay_packet(self, packet).await
    }
}
