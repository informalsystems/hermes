use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::std_prelude::*;

// pub trait FilterContext: RelayContext {
//     fn should_relay(&self, packet: &Self::Packet) -> bool;
// }

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: RelayContext,
{
    async fn should_relay_packet(
        &self,
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}
pub struct AndPacketFilter<FilterA, FilterB> {
    pub filter_a: FilterA,
    pub filter_b: FilterB,
}

#[async_trait]
impl<FilterA, FilterB, Relay> PacketFilter<Relay> for AndPacketFilter<FilterA, FilterB>
where
    Relay: RelayContext,
    FilterA: PacketFilter<Relay>,
    FilterB: PacketFilter<Relay>,
{
    async fn should_relay_packet(
        &self,
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(self.filter_a.should_relay_packet(relay, packet).await?
            && self.filter_b.should_relay_packet(relay, packet).await?)
    }
}

pub struct OrPacketFilter<FilterA, FilterB> {
    pub filter_a: FilterA,
    pub filter_b: FilterB,
}

#[async_trait]
impl<FilterA, FilterB, Relay> PacketFilter<Relay> for OrPacketFilter<FilterA, FilterB>
where
    Relay: RelayContext,
    FilterA: PacketFilter<Relay>,
    FilterB: PacketFilter<Relay>,
{
    async fn should_relay_packet(
        &self,
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(self.filter_a.should_relay_packet(relay, packet).await?
            || self.filter_b.should_relay_packet(relay, packet).await?)
    }
}
