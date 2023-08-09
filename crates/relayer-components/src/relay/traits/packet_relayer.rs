use async_trait::async_trait;

use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait PacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayPacket: HasRelayPacket {
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanRelayPacket for Relay
where
    Relay: HasRelayPacket + HasComponents,
    Relay::Components: PacketRelayer<Relay>,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        Relay::Components::relay_packet(self, packet).await
    }
}

#[macro_export]
macro_rules! derive_packet_relayer {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, $( $( $param ),* )*>
            $crate::relay::traits::packet_relayer::PacketRelayer<Relay>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::packet::HasRelayPacket,
            $source: $crate::relay::traits::packet_relayer::PacketRelayer<Relay>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
                <$source as $crate::relay::traits::packet_relayer::PacketRelayer<Relay>>
                    ::relay_packet(relay, packet).await
            }
        }

    };
}
