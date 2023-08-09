use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

#[async_trait]
pub trait ReceivePacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>;
}

#[async_trait]
pub trait CanRelayReceivePacket: HasRelayPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &Height<Self::SrcChain>,
        packet: &Self::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>>, Self::Error>;
}

#[async_trait]
impl<Relay> CanRelayReceivePacket for Relay
where
    Relay: HasRelayPacket + HasComponents,
    Relay::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
    Relay::Components: ReceivePacketRelayer<Relay>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>
    {
        Relay::Components::relay_receive_packet(self, source_height, packet).await
    }
}

#[macro_export]
macro_rules! derive_receive_packet_relayer {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $source:ty $(,)?  ) => {
        #[$crate::vendor::async_trait::async_trait]
        impl<Relay, $( $( $param ),* )*>
            $crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer<Relay>
            for $target $( < $( $param ),* > )*
        where
            Relay: $crate::relay::traits::packet::HasRelayPacket,
            Relay::DstChain: $crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent<Relay::SrcChain>,
            $source: $crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer<Relay>,
            $target $( < $( $param ),* > )*: $crate::core::traits::sync::Async,
        {
            async fn relay_receive_packet(
                relay: &Relay,
                source_height: &<Relay::SrcChain as $crate::chain::traits::types::height::HasHeightType>::Height,
                packet: &Relay::Packet,
            ) -> Result<Option<<Relay::DstChain as $crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent<Relay::SrcChain>>::WriteAcknowledgementEvent>, Relay::Error> {
                <$source as $crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayer<Relay>>
                    ::relay_receive_packet(relay, source_height, packet).await
            }
        }

    };
}
