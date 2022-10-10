use async_trait::async_trait;

use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::core::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: RelayContext,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

#[async_trait]
pub trait HasPacketFilter: RelayContext {
    type PacketFilter: PacketFilter<Self>;

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Self::PacketFilter::should_relay_packet(self, packet).await
    }
}
