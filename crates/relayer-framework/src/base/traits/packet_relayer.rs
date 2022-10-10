use async_trait::async_trait;

use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::core::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: RelayContext,
{
    async fn relay_packet(context: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

pub trait HasPacketRelayer: RelayContext {
    type PacketRelayer: PacketRelayer<Self>;
}
