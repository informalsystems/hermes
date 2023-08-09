use async_trait::async_trait;

use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

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
pub trait CanFilterPackets: HasRelayPacket {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;
}

#[async_trait]
impl<Relay> CanFilterPackets for Relay
where
    Relay: HasRelayPacket + HasComponents,
    Relay::Components: PacketFilter<Relay>,
{
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Relay::Components::should_relay_packet(self, packet).await
    }
}

#[macro_export]
macro_rules! derive_packet_filter {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, $( $( $param ),* )*>
            $crate::relay::traits::packet_filter::PacketFilter<Relay>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::packet::HasRelayPacket,
            $source: $crate::relay::traits::packet_filter::PacketFilter<Relay>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn should_relay_packet(
                relay: &Relay,
                packet: &Relay::Packet,
            ) -> Result<bool, Relay::Error> {
                <$source as $crate::relay::traits::packet_filter::PacketFilter<Relay>>
                    ::should_relay_packet(relay, packet).await
            }
        }

    };
}
