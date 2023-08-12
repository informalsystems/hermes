use async_trait::async_trait;

use crate::core::traits::component::HasComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct PacketFilterComponent;

#[async_trait]
pub trait PacketFilter<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

#[async_trait]
impl<Relay, Component> PacketFilter<Relay> for Component
where
    Relay: HasRelayPacket,
    Component: HasComponent<PacketFilterComponent>,
    Component::Component: PacketFilter<Relay>,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        Component::Component::should_relay_packet(relay, packet).await
    }
}

#[async_trait]
pub trait CanFilterPackets: HasRelayPacket {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;
}

#[async_trait]
impl<Relay> CanFilterPackets for Relay
where
    Relay: HasRelayPacket + HasComponent<PacketFilterComponent>,
    Relay::Component: PacketFilter<Relay>,
{
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Relay::Component::should_relay_packet(self, packet).await
    }
}