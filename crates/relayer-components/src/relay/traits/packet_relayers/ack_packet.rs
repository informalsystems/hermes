use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait AckPacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        context: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait CanRelayAckPacket: HasRelayPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanRelayAckPacket for Relay
where
    Relay: HasRelayPacket + HasComponents,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Relay::Components: AckPacketRelayer<Relay>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error> {
        Relay::Components::relay_ack_packet(self, destination_height, packet, ack).await
    }
}

#[macro_export]
macro_rules! derive_ack_packet_relayer {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, $( $( $param ),* )*>
            $crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayer<Relay>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::packet::HasRelayPacket,
            Relay::DstChain: $crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent<Relay::SrcChain>,
            $source: $crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayer<Relay>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn relay_ack_packet(
                relay: &Relay,
                destination_height: &<Relay::DstChain as $crate::chain::traits::types::height::HasHeightType>::Height,
                packet: &Relay::Packet,
                ack: &<Relay::DstChain as $crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent<Relay::SrcChain>>::WriteAcknowledgementEvent,
            ) -> Result<(), Relay::Error> {
                <$source as $crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayer<Relay>>
                    ::relay_ack_packet(relay, destination_height, packet, ack).await
            }
        }

    };
}
