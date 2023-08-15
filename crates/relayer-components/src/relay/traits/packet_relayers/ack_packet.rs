use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::core::traits::component::DelegateComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct AckPacketRelayerComponent;

#[async_trait]
pub trait AckPacketRelayer<Relay>: Async
where
    Relay: HasRelayPacket,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
{
    async fn relay_ack_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Relay, Component> AckPacketRelayer<Relay> for Component
where
    Relay: HasRelayPacket,
    Component: DelegateComponent<AckPacketRelayerComponent>,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Component::Delegate: AckPacketRelayer<Relay>,
{
    async fn relay_ack_packet(
        relay: &Relay,
        destination_height: &Height<Relay::DstChain>,
        packet: &Relay::Packet,
        ack: &WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>,
    ) -> Result<(), Relay::Error> {
        Component::Delegate::relay_ack_packet(relay, destination_height, packet, ack).await
    }
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
    Relay: HasRelayPacket + DelegateComponent<AckPacketRelayerComponent>,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Relay::Delegate: AckPacketRelayer<Relay>,
{
    async fn relay_ack_packet(
        &self,
        destination_height: &Height<Self::DstChain>,
        packet: &Self::Packet,
        ack: &WriteAcknowledgementEvent<Self::DstChain, Self::SrcChain>,
    ) -> Result<(), Self::Error> {
        Relay::Delegate::relay_ack_packet(self, destination_height, packet, ack).await
    }
}
