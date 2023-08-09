use async_trait::async_trait;

use crate::chain::types::aliases::Height;
use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait TimeoutUnorderedPacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn relay_timeout_unordered_packet(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
    ) -> Result<(), Relay::Error>;
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
    Relay: HasRelayPacket + HasComponents,
    Relay::Components: TimeoutUnorderedPacketRelayer<Relay>,
{
    async fn relay_timeout_unordered_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
    ) -> Result<(), Self::Error> {
        Relay::Components::relay_timeout_unordered_packet(self, destination_height, packet).await
    }
}

#[macro_export]
macro_rules! derive_timeout_unordered_packet_relayer {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, $( $( $param ),* )*>
            $crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer<Relay>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::packet::HasRelayPacket,
            $source: $crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer<Relay>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn relay_timeout_unordered_packet(
                relay: &Relay,
                destination_height: &<Relay::DstChain as $crate::chain::traits::types::height::HasHeightType>::Height,
                packet: &Relay::Packet,
            ) -> Result<(), Relay::Error> {
                <$source as $crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayer<Relay>>
                    ::relay_timeout_unordered_packet(relay, destination_height, packet).await
            }
        }

    };
}
