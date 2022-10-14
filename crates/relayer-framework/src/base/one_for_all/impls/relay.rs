use async_trait::async_trait;

use crate::base::chain::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::runtime::HasRuntime;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaBaseChainTypes};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::retry::SupportsPacketRetry;
use crate::base::relay::traits::context::HasRelayTypes;
use crate::base::relay::traits::ibc_message_sender::InjectMismatchIbcEventsCountError;
use crate::base::relay::traits::messages::ack_packet::{
    AckPacketMessageBuilder, HasAckPacketMessageBuilder,
};
use crate::base::relay::traits::messages::receive_packet::{
    HasReceivePacketMessageBuilder, ReceivePacketMessageBuilder,
};
use crate::base::relay::traits::messages::timeout_packet::{
    HasTimeoutUnorderedPacketMessageBuilder, TimeoutUnorderedPacketMessageBuilder,
};
use crate::base::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

impl<Relay: OfaBaseRelay> HasError for OfaRelayWrapper<Relay> {
    type Error = Relay::Error;
}

impl<Relay: OfaBaseRelay> HasRuntime for OfaRelayWrapper<Relay> {
    type Runtime = OfaRuntimeContext<Relay::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.relay.runtime()
    }
}

impl<Relay: OfaBaseRelay> HasRelayTypes for OfaRelayWrapper<Relay> {
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

    fn source_client_id(&self) -> &<Relay::SrcChain as OfaBaseChainTypes>::ClientId {
        self.relay.src_client_id()
    }

    fn destination_client_id(&self) -> &<Relay::DstChain as OfaBaseChainTypes>::ClientId {
        self.relay.dst_client_id()
    }
}

pub struct OfaUpdateClientMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
    for OfaUpdateClientMessageBuilder
where
    Relay: OfaBaseRelay<SrcChain = SrcChain>,
    SrcChain: OfaBaseChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        height: &<Relay::DstChain as OfaBaseChainTypes>::Height,
    ) -> Result<Vec<SrcChain::Message>, Relay::Error> {
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
    Relay: OfaBaseRelay<DstChain = DstChain>,
    DstChain: OfaBaseChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        height: &<Relay::SrcChain as OfaBaseChainTypes>::Height,
    ) -> Result<Vec<DstChain::Message>, Relay::Error> {
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
    Relay: OfaBaseRelay<DstChain = DstChain>,
    DstChain: OfaBaseChain,
{
    async fn build_receive_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        height: &<Relay::SrcChain as OfaBaseChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<DstChain::Message, Relay::Error> {
        let message = relay
            .relay
            .build_receive_packet_message(height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaBaseRelay> HasReceivePacketMessageBuilder for OfaRelayWrapper<Relay> {
    type ReceivePacketMessageBuilder = OfaReceivePacketMessageBuilder;
}

pub struct OfaAckPacketMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> AckPacketMessageBuilder<OfaRelayWrapper<Relay>> for OfaAckPacketMessageBuilder
where
    Relay: OfaBaseRelay<SrcChain = SrcChain>,
    SrcChain: OfaBaseChain,
{
    async fn build_ack_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaBaseChainTypes>::Height,
        packet: &Relay::Packet,
        ack: &<Relay::DstChain as OfaBaseChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<SrcChain::Message, Relay::Error> {
        let message = relay
            .relay
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaBaseRelay> HasAckPacketMessageBuilder for OfaRelayWrapper<Relay> {
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
    Relay: OfaBaseRelay<DstChain = DstChain, SrcChain = SrcChain>,
    DstChain: OfaBaseChain,
    SrcChain: OfaBaseChain,
{
    async fn build_timeout_unordered_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaBaseChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<SrcChain::Message, Relay::Error> {
        let message = relay
            .relay
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay, InMessageBuilder, Target> HasTimeoutUnorderedPacketMessageBuilder
    for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    InMessageBuilder: TimeoutUnorderedPacketMessageBuilder<Relay>,
    Target: ChainTarget<Relay, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
{
    type TimeoutUnorderedPacketMessageBuilder =
        WaitTimeoutUnorderedTimeoutPacketMessageBuilder<InMessageBuilder, Target>;
}

impl<Relay: OfaBaseRelay> SupportsPacketRetry for OfaRelayWrapper<Relay> {
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Self::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        Relay::max_retry_exceeded_error(e)
    }
}

impl<Relay: OfaBaseRelay> InjectMismatchIbcEventsCountError for OfaRelayWrapper<Relay> {
    fn mismatch_ibc_events_count_error(expected: usize, actual: usize) -> Self::Error {
        Relay::mismatch_ibc_events_count_error(expected, actual)
    }
}
