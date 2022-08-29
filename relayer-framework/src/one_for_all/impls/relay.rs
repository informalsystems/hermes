use async_trait::async_trait;

use crate::core::traits::contexts::error::HasError;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::contexts::runtime::HasRuntime;
use crate::core::traits::messages::ack_packet::{
    AckPacketMessageBuilder, HasAckPacketMessageBuilder,
};
use crate::core::traits::messages::receive_packet::{
    HasReceivePacketMessageBuilder, ReceivePacketMessageBuilder,
};
use crate::core::traits::messages::timeout_packet::TimeoutUnorderedPacketMessageBuilder;
use crate::core::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::core::traits::target::{DestinationTarget, SourceTarget};
use crate::core::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};
use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext};
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::traits::relay::OfaRelayContext;
use crate::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::std_prelude::*;

impl<Relay: OfaRelay> HasError for OfaRelayContext<Relay> {
    type Error = OfaErrorContext<Relay::Error>;
}

impl<Relay: OfaRelay> HasRuntime for OfaRelayContext<Relay> {
    type Runtime = OfaRuntimeContext<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }
}

impl<Relay: OfaRelay> RelayContext for OfaRelayContext<Relay> {
    type SrcChain = OfaChainContext<Relay::SrcChain>;

    type DstChain = OfaChainContext<Relay::DstChain>;

    type Packet = Relay::Packet;

    fn packet_src_port(packet: &Self::Packet) -> &PortId<Self::SrcChain, Self::DstChain> {
        Relay::packet_src_port(packet)
    }

    fn packet_src_channel_id(packet: &Self::Packet) -> &ChannelId<Self::SrcChain, Self::DstChain> {
        Relay::packet_src_channel_id(packet)
    }

    fn packet_dst_port(packet: &Self::Packet) -> &PortId<Self::DstChain, Self::SrcChain> {
        Relay::packet_dst_port(packet)
    }

    fn packet_dst_channel_id(packet: &Self::Packet) -> &ChannelId<Self::DstChain, Self::SrcChain> {
        Relay::packet_dst_channel_id(packet)
    }

    fn packet_sequence(packet: &Self::Packet) -> &Sequence<Self::SrcChain, Self::DstChain> {
        Relay::packet_sequence(packet)
    }

    fn packet_timeout_height(packet: &Self::Packet) -> Option<&Height<Self::DstChain>> {
        Relay::packet_timeout_height(packet)
    }

    fn packet_timeout_timestamp(packet: &Self::Packet) -> &Timestamp<Self::DstChain> {
        Relay::packet_timeout_timestamp(packet)
    }

    fn source_chain(&self) -> &Self::SrcChain {
        self.relay.src_chain()
    }

    fn destination_chain(&self) -> &Self::DstChain {
        self.relay.dst_chain()
    }

    fn source_client_id(&self) -> &<Relay::SrcChain as OfaChain>::ClientId {
        self.relay.src_client_id()
    }

    fn destination_client_id(&self) -> &<Relay::DstChain as OfaChain>::ClientId {
        self.relay.dst_client_id()
    }
}

pub struct OfaUpdateClientMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> UpdateClientMessageBuilder<OfaRelayContext<Relay>, SourceTarget>
    for OfaUpdateClientMessageBuilder
where
    Relay: OfaRelay<SrcChain = SrcChain>,
    SrcChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayContext<Relay>,
        height: &<Relay::DstChain as OfaChain>::Height,
    ) -> Result<Vec<SrcChain::Message>, OfaErrorContext<Relay::Error>> {
        let messages = context
            .relay
            .build_src_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

#[async_trait]
impl<Relay, DstChain> UpdateClientMessageBuilder<OfaRelayContext<Relay>, DestinationTarget>
    for OfaUpdateClientMessageBuilder
where
    Relay: OfaRelay<DstChain = DstChain>,
    DstChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayContext<Relay>,
        height: &<Relay::SrcChain as OfaChain>::Height,
    ) -> Result<Vec<DstChain::Message>, OfaErrorContext<Relay::Error>> {
        let messages = context
            .relay
            .build_dst_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

pub struct OfaReceivePacketMessageBuilder;

#[async_trait]
impl<Relay, DstChain> ReceivePacketMessageBuilder<OfaRelayContext<Relay>>
    for OfaReceivePacketMessageBuilder
where
    Relay: OfaRelay<DstChain = DstChain>,
    DstChain: OfaChain,
{
    async fn build_receive_packet_message(
        relay: &OfaRelayContext<Relay>,
        height: &<Relay::SrcChain as OfaChain>::Height,
        packet: &Relay::Packet,
    ) -> Result<DstChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_receive_packet_message(height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaRelay> HasReceivePacketMessageBuilder for OfaRelayContext<Relay> {
    type ReceivePacketMessageBuilder = OfaReceivePacketMessageBuilder;
}

pub struct OfaAckPacketMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> AckPacketMessageBuilder<OfaRelayContext<Relay>> for OfaAckPacketMessageBuilder
where
    Relay: OfaRelay<SrcChain = SrcChain>,
    SrcChain: OfaChain,
{
    async fn build_ack_packet_message(
        relay: &OfaRelayContext<Relay>,
        destination_height: &<Relay::DstChain as OfaChain>::Height,
        packet: &Relay::Packet,
        ack: &<Relay::DstChain as OfaChain>::WriteAcknowledgementEvent,
    ) -> Result<SrcChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaRelay> HasAckPacketMessageBuilder for OfaRelayContext<Relay> {
    type AckPacketMessageBuilder = OfaAckPacketMessageBuilder;
}

pub struct OfaTimeoutUnorderedPacketMessageBuilder; 

#[async_trait]
impl<Relay, DstChain, SrcChain> TimeoutUnorderedPacketMessageBuilder<OfaRelayContext<Relay>> 
    for OfaTimeoutUnorderedPacketMessageBuilder 
where
    Relay: OfaRelay<DstChain=DstChain, SrcChain=SrcChain>,
    DstChain: OfaChain,
    SrcChain: OfaChain,
{
    async fn build_timeout_unordered_packet_message(
        relay: &OfaRelayContext<Relay>,
        height: &<Relay::DstChain as OfaChain>::Height,
        packet: &Relay::Packet,
    ) -> Result<SrcChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_timeout_unordered_packet_message(height, packet)
            .await?;

        Ok(message)
    }
}
