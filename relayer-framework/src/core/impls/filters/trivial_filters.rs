use async_trait::async_trait;
use core::marker::PhantomData;
use crate::std_prelude::*;

use crate::core::traits::contexts::{filter::PacketFilter, relay::RelayContext};



pub struct AlwaysFalsePacketFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for AlwaysFalsePacketFilter
where Relay: RelayContext {
    async fn should_relay_packet(
        _relay: &Relay,
        _packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(false)
    }
}

pub struct AlwaysTruePacketFilter;

#[async_trait]
impl<Relay> PacketFilter<Relay> for AlwaysTruePacketFilter
where Relay: RelayContext {
    async fn should_relay_packet(
        _relay: &Relay,
        _packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(true)
    }
}

pub struct NegationPacketFilter<Filter>(PhantomData<(Filter)>);

#[async_trait]
impl<Relay, Filter> PacketFilter<Relay> for NegationPacketFilter<Filter> 
where Relay: RelayContext, 
Filter: PacketFilter<Relay>, 
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(!Filter::should_relay_packet(relay, packet).await?)
    }
}

pub struct AndPacketFilter<FilterA, FilterB>(PhantomData<(FilterA, FilterB)>);

#[async_trait]
impl<Relay, FilterA, FilterB> PacketFilter<Relay> for AndPacketFilter<FilterA, FilterB> 
where Relay: RelayContext, 
FilterA: PacketFilter<Relay>, 
FilterB: PacketFilter<Relay> 
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(FilterA::should_relay_packet(relay, packet).await? && FilterB::should_relay_packet(relay, packet).await?)
    }
}

pub struct OrPacketFilter<FilterA, FilterB>(PhantomData<(FilterA, FilterB)>);

#[async_trait]
impl<Relay, FilterA, FilterB> PacketFilter<Relay> for OrPacketFilter<FilterA, FilterB> 
where Relay: RelayContext, 
FilterA: PacketFilter<Relay>, 
FilterB: PacketFilter<Relay> 
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Ok(FilterA::should_relay_packet(relay, packet).await? || FilterB::should_relay_packet(relay, packet).await?)
    }
}