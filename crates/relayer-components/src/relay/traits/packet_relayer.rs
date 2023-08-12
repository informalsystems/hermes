use async_trait::async_trait;

use crate::core::traits::component::HasComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct PacketRelayerComponent;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Component, Relay> PacketRelayer<Relay> for Component
where
    Relay: HasRelayPacket,
    Component: HasComponent<PacketRelayerComponent>,
    Component::Component: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        Component::Component::relay_packet(relay, packet).await
    }
}

#[async_trait]
pub trait CanRelayPacket: HasRelayPacket {
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanRelayPacket for Relay
where
    Relay: HasRelayPacket + HasComponent<PacketRelayerComponent>,
    Relay::Component: PacketRelayer<Relay>,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Relay::Component::relay_packet(self, packet).await
    }
}