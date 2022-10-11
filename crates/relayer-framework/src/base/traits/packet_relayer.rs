use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::traits::contexts::relay::RelayContext;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: RelayContext,
{
    async fn relay_packet(context: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait HasPacketRelayer: RelayContext {
    type PacketRelayer: PacketRelayer<Self>;

    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Self::PacketRelayer::relay_packet(self, packet).await
    }
}
