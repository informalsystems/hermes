use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::std_prelude::*;

// pub trait FilterContext: RelayContext {
//     fn should_relay(&self, packet: &Self::Packet) -> bool;
// }

#[async_trait]
pub trait PacketFilter<Relay> : Async
where
    Relay: RelayContext,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

/*
If the packet filter must be part of the relay context
#[async_trait]
pub trait HasPacketFilter: RelayContext {
    type PacketFilter: PacketFilter<Self>;

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Self::PacketFilter::should_relay_packet(self, packet).await
    }
}
*/