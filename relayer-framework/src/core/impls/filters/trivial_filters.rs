use async_trait::async_trait;

use crate::core::traits::contexts::filter::PacketFilter;
use crate::core::traits::contexts::relay::RelayContext;
use crate::std_prelude::*;

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
    async fn should_relay_packet(&self, packet: &Relay::Packet) -> Result<bool, Relay::Error> {
        Ok(self.filter_a.should_relay_packet(packet).await?
            && self.filter_b.should_relay_packet(packet).await?)
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
    async fn should_relay_packet(&self, packet: &Relay::Packet) -> Result<bool, Relay::Error> {
        Ok(self.filter_a.should_relay_packet(packet).await?
            || self.filter_b.should_relay_packet(packet).await?)
    }
}

pub struct EmptyFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for EmptyFilter
where
    Relay: RelayContext,
{
    async fn should_relay_packet(&self, _packet: &Relay::Packet) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}

pub struct AllowFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for AllowFilter
where
    Relay: RelayContext,
{
    async fn should_relay_packet(&self, _packet: &Relay::Packet) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}