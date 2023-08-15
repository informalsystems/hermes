use async_trait::async_trait;

use crate::chain::types::aliases::Height;
use crate::core::traits::component::DelegateComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct TimeoutUnorderedPacketRelayerComponent;

#[async_trait]
pub trait TimeoutUnorderedPacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn relay_timeout_unordered_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Relay, Component> TimeoutUnorderedPacketRelayer<Relay> for Component
where
    Relay: HasRelayPacket,
    Component: DelegateComponent<TimeoutUnorderedPacketRelayerComponent>,
    Component::Delegate: TimeoutUnorderedPacketRelayer<Relay>,
{
    async fn relay_timeout_unordered_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error> {
        Component::Delegate::relay_timeout_unordered_packet(relay, destination_height, packet).await
    }
}

/// Encapsulates the capability of a relayer to send timeout packets over
/// unordered channels.
///
/// Timeout packets are sent from a destination chain to the source chain that
/// originated the timed out message.
///
/// When a timeout packet is sent, a response is not expected to be received.
/// This is in contrast when sending e.g. receive packets, which expect to
/// receive back a `WriteAcknowledgementEvent` in response to the receive
/// packet.
#[async_trait]
pub trait CanRelayTimeoutUnorderedPacket: HasRelayPacket {
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanRelayTimeoutUnorderedPacket for Relay
where
    Relay: HasRelayPacket + DelegateComponent<TimeoutUnorderedPacketRelayerComponent>,
    Relay::Delegate: TimeoutUnorderedPacketRelayer<Relay>,
{
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error> {
        Relay::Delegate::relay_timeout_unordered_packet(self, destination_height, packet).await
    }
}
