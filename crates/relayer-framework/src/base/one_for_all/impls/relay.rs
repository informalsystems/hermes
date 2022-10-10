use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainTypes, OfaChainWrapper};
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::one_for_all::traits::relay::OfaRelay;
use crate::base::one_for_all::traits::relay::OfaRelayWrapper;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::traits::contexts::error::HasError;
use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::contexts::runtime::HasRuntime;
use crate::base::traits::messages::ack_packet::{
    AckPacketMessageBuilder, HasAckPacketMessageBuilder,
};
use crate::base::traits::messages::receive_packet::{
    HasReceivePacketMessageBuilder, ReceivePacketMessageBuilder,
};
use crate::base::traits::messages::timeout_packet::{
    HasTimeoutUnorderedPacketMessageBuilder, TimeoutUnorderedPacketMessageBuilder,
};
use crate::base::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::base::traits::target::{DestinationTarget, SourceTarget};
use crate::base::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};
use crate::std_prelude::*;

impl<Relay: OfaRelay> HasError for OfaRelayWrapper<Relay> {
    type Error = OfaErrorContext<Relay::Error>;
}

impl<Relay: OfaRelay> HasRuntime for OfaRelayWrapper<Relay> {
    type Runtime = OfaRuntimeContext<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }
}

impl<Relay: OfaRelay> RelayContext for OfaRelayWrapper<Relay> {
    type SrcChain = OfaChainWrapper<Relay::SrcChain>;

    type DstChain = OfaChainWrapper<Relay::DstChain>;

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

    fn source_client_id(&self) -> &<Relay::SrcChain as OfaChainTypes>::ClientId {
        self.relay.src_client_id()
    }

    fn destination_client_id(&self) -> &<Relay::DstChain as OfaChainTypes>::ClientId {
        self.relay.dst_client_id()
    }
}

pub struct OfaUpdateClientMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
    for OfaUpdateClientMessageBuilder
where
    Relay: OfaRelay<SrcChain = SrcChain>,
    SrcChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        height: &<Relay::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<SrcChain::Message>, OfaErrorContext<Relay::Error>> {
        let messages = context
            .relay
            .build_src_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

#[async_trait]
impl<Relay, DstChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, DestinationTarget>
    for OfaUpdateClientMessageBuilder
where
    Relay: OfaRelay<DstChain = DstChain>,
    DstChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        height: &<Relay::SrcChain as OfaChainTypes>::Height,
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
impl<Relay, DstChain> ReceivePacketMessageBuilder<OfaRelayWrapper<Relay>>
    for OfaReceivePacketMessageBuilder
where
    Relay: OfaRelay<DstChain = DstChain>,
    DstChain: OfaChain,
{
    async fn build_receive_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        height: &<Relay::SrcChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<DstChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_receive_packet_message(height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaRelay> HasReceivePacketMessageBuilder for OfaRelayWrapper<Relay> {
    type ReceivePacketMessageBuilder = OfaReceivePacketMessageBuilder;
}

pub struct OfaAckPacketMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> AckPacketMessageBuilder<OfaRelayWrapper<Relay>> for OfaAckPacketMessageBuilder
where
    Relay: OfaRelay<SrcChain = SrcChain>,
    SrcChain: OfaChain,
{
    async fn build_ack_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
        ack: &<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<SrcChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaRelay> HasAckPacketMessageBuilder for OfaRelayWrapper<Relay> {
    type AckPacketMessageBuilder = OfaAckPacketMessageBuilder;
}

/// Implements the timeout packet message builder that constructs timeout packets
/// to be sent over unordered channels between chains that implement the
/// [`one_for_all`] trait.
pub struct OfaTimeoutUnorderedPacketMessageBuilder;

#[async_trait]
impl<Relay, DstChain, SrcChain> TimeoutUnorderedPacketMessageBuilder<OfaRelayWrapper<Relay>>
    for OfaTimeoutUnorderedPacketMessageBuilder
where
    Relay: OfaRelay<DstChain = DstChain, SrcChain = SrcChain>,
    DstChain: OfaChain,
    SrcChain: OfaChain,
{
    async fn build_timeout_unordered_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<SrcChain::Message, OfaErrorContext<Relay::Error>> {
        let message = relay
            .relay
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaRelay> HasTimeoutUnorderedPacketMessageBuilder for OfaRelayWrapper<Relay> {
    type TimeoutUnorderedPacketMessageBuilder = OfaTimeoutUnorderedPacketMessageBuilder;
}
