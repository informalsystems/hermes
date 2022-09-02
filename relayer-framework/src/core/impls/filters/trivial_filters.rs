use async_trait::async_trait;
use core::marker::PhantomData;
use crate::std_prelude::*;

use crate::core::traits::contexts::{filter::PacketFilter, relay::RelayContext};


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