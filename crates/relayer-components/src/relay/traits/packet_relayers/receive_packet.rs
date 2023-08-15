use async_trait::async_trait;

use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::types::aliases::{Height, WriteAcknowledgementEvent};
use crate::core::traits::component::DelegateComponent;
use crate::core::traits::sync::Async;
use crate::relay::traits::packet::HasRelayPacket;
use crate::std_prelude::*;

pub struct ReceivePacketRelayerComponnent;

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
impl<Relay, Component> ReceivePacketRelayer<Relay> for Component
where
    Relay: HasRelayPacket,
    Component: DelegateComponent<ReceivePacketRelayerComponnent>,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Component::Delegate: ReceivePacketRelayer<Relay>,
{
    async fn relay_receive_packet(
        relay: &Relay,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>
    {
        Component::Delegate::relay_receive_packet(relay, source_height, packet).await
    }
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
    Relay: HasRelayPacket + DelegateComponent<ReceivePacketRelayerComponnent>,
    Relay::DstChain: HasWriteAcknowledgementEvent<Relay::SrcChain>,
    Relay::Delegate: ReceivePacketRelayer<Relay>,
{
    async fn relay_receive_packet(
        &self,
        source_height: &Height<Relay::SrcChain>,
        packet: &Relay::Packet,
    ) -> Result<Option<WriteAcknowledgementEvent<Relay::DstChain, Relay::SrcChain>>, Relay::Error>
    {
        Relay::Delegate::relay_receive_packet(self, source_height, packet).await
    }
}
