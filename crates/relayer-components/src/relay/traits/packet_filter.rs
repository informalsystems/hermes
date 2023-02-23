use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

#[async_trait]
pub trait CanFilterPackets: HasRelayTypes {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;
}
