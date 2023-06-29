//! The `OfaChainWrapper` trait specifies what a chain context needs to provide
//! in order to gain access to the APIs provided by the `AfoBaseChain`
//! trait.

use alloc::sync::Arc;
use core::fmt::{Debug, Display};
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::logger::traits::logger::BaseLogger;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::subscription::Subscription;

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::traits::telemetry::OfaTelemetry;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::one_for_all::types::telemetry::OfaTelemetryWrapper;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaChain: Async {
    /**
       Corresponds to
       [`HasErrorType::Error`](ibc_relayer_components::core::traits::error::HasErrorType::Error).
    */
    type Error: Async + Debug;

    /**
       Corresponds to
       [`HasRuntime::Runtime`](ibc_relayer_components::runtime::traits::runtime::HasRuntime::Runtime).
    */
    type Runtime: OfaRuntime;

    type Logger: HasBaseLogLevels;

    type Telemetry: OfaTelemetry;

    /**
       Corresponds to
       [`HasChainTypes::Height`](ibc_relayer_components::chain::traits::types::height::HasHeightType::Height).
    */
    type Height: Clone + Ord + Display + Async;

    /**
       Corresponds to
       [`HasChainTypes::Timestamp`](ibc_relayer_components::chain::traits::types::timestamp::HasTimestampType::Timestamp).
    */
    type Timestamp: Ord + Display + Async;

    /**
       Corresponds to
       [`HasMessageType::Message`](ibc_relayer_components::chain::traits::types::message::HasMessageType::Message).
    */
    type Message: Async;

    /**
       Corresponds to
       [`HasEventType::Event`](ibc_relayer_components::chain::traits::types::event::HasEventType::Event).
    */
    type Event: Async;

    /**
       Corresponds to
       [`HasChainIdType::ChainId`](ibc_relayer_components::chain::traits::types::chain_id::HasChainIdType::ChainId).
    */
    type ChainId: Eq + Ord + Display + Clone + Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ClientId`](ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes::ClientId).
    */
    type ClientId: Ord + Display + Clone + Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ConnectionId`](ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes::ConnectionId).
    */
    type ConnectionId: Display + Clone + Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::ChannelId`](ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes::ChannelId).
    */
    type ChannelId: Display + Clone + Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::PortId`](ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes::PortId).
    */
    type PortId: Display + Clone + Async;

    /**
       Corresponds to
       [`HasIbcChainTypes::Sequence`](ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes::Sequence).
    */
    type Sequence: Display + Clone + Async;

    /**
       Corresponds to
       [`HasChainStatusType::ChainStatus`](ibc_relayer_components::chain::traits::types::status::HasChainStatusType::ChainStatus).
    */
    type ChainStatus: Async;

    /**
       Corresponds to
       [`HasConsensusStateType::ConsensusState`](ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType::ConsensusState).
    */
    type ConsensusState: Async;

    /**
       Corresponds to
       [`HasWriteAcknowledgementEvent::WriteAcknowledgementEvent`](ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent::WriteAcknowledgementEvent).
    */
    type WriteAcknowledgementEvent: Async;

    type SendPacketEvent: Async;

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;

    fn log_event<'a>(event: &'a Self::Event) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error>;

    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error>;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;

    /**
       Corresponds to
       [`CanSendMessages::send_messages`](ibc_relayer_components::chain::traits::message_sender::CanSendMessages::send_messages)
    */
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;

    fn chain_id(&self) -> &Self::ChainId;

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error>;

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaChain
where
    Counterparty: OfaIbcChain<Self>,
{
    /**
       Corresponds to
       [`HasIbcPacketTypes::IncomingPacket`](ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes::IncomingPacket)
    */
    type IncomingPacket: Async;

    /**
       Corresponds to
       [`HasIbcPacketTypes::OutgoingPacket`](ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes::OutgoingPacket)
    */
    type OutgoingPacket: Async;

    type ConnectionDetails: Async;

    type ConnectionVersion: Eq + Default + Async;

    type InitConnectionOptions: Async;

    type ConnectionOpenInitPayload: Async;

    type ConnectionOpenTryPayload: Async;

    type ConnectionOpenAckPayload: Async;

    type ConnectionOpenConfirmPayload: Async;

    fn incoming_packet_src_channel_id(packet: &Self::IncomingPacket) -> &Counterparty::ChannelId;

    fn incoming_packet_dst_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId;

    fn incoming_packet_src_port(packet: &Self::IncomingPacket) -> &Counterparty::PortId;

    fn incoming_packet_dst_port(packet: &Self::IncomingPacket) -> &Self::PortId;

    fn incoming_packet_sequence(packet: &Self::IncomingPacket) -> &Counterparty::Sequence;

    fn incoming_packet_timeout_height(packet: &Self::IncomingPacket) -> Option<&Self::Height>;

    fn incoming_packet_timeout_timestamp(packet: &Self::IncomingPacket) -> &Self::Timestamp;

    fn outgoing_packet_src_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId;

    fn outgoing_packet_dst_channel_id(packet: &Self::OutgoingPacket) -> &Counterparty::ChannelId;

    fn outgoing_packet_src_port(packet: &Self::OutgoingPacket) -> &Self::PortId;

    fn outgoing_packet_dst_port(packet: &Self::OutgoingPacket) -> &Counterparty::PortId;

    fn outgoing_packet_sequence(packet: &Self::OutgoingPacket) -> &Self::Sequence;

    fn outgoing_packet_timeout_height(
        packet: &Self::OutgoingPacket,
    ) -> Option<&Counterparty::Height>;

    fn outgoing_packet_timeout_timestamp(packet: &Self::OutgoingPacket)
        -> &Counterparty::Timestamp;

    fn log_incoming_packet<'a>(
        event: &'a Self::IncomingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn log_outgoing_packet<'a>(
        event: &'a Self::OutgoingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height>;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent>;

    fn extract_packet_from_send_packet_event(event: &Self::SendPacketEvent)
        -> Self::OutgoingPacket;

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket;

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Counterparty::ChainId, Self::Error>;

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;

    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error>;

    async fn query_write_acknowledgement_event(
        &self,
        packet: &Self::IncomingPacket,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;

    async fn build_receive_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Counterparty::Message, Self::Error>;

    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;

    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<Self::ConnectionOpenInitPayload, Self::Error>;

    async fn build_connection_open_try_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error>;

    async fn build_connection_open_ack_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error>;

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error>;

    async fn build_connection_open_init_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: Counterparty::ConnectionOpenInitPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_try_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenTryPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenAckPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error>;
}
