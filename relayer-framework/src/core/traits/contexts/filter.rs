use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::std_prelude::*;

// pub trait FilterContext: RelayContext {
//     fn should_relay(&self, packet: &Self::Packet) -> bool;
// }

pub trait HasPacketFilter: Async {
    type Filter: Async;

    fn filter(&self) -> &Self::Filter;
}

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: RelayContext,
{
    async fn should_relay_packet(&self, packet: &Relay::Packet) -> Result<bool, Relay::Error>;
}
