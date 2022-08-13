use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::core::Async;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: RelayContext,
{
    async fn relay_packet(
        &self,
        context: &Relay,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error>;
}

pub trait HasPacketRelayer: RelayContext {
    type PacketRelayer: PacketRelayer<Self>;
}
