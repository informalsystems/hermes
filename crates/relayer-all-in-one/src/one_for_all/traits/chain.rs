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
pub trait OfaChainTypes: Async {
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
       [`HasMessageType::Message`](ibc_relayer_components::chain::traits::types::message::HasMessageType::Message).
    */
    type Message: Async;

    /**
       Corresponds to
       [`HasEventType::Event`](ibc_relayer_components::chain::traits::types::event::HasEventType::Event).
    */
    type Event: Async;

    type ClientState: Async;

    /**
       Corresponds to
       [`HasConsensusStateType::ConsensusState`](ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType::ConsensusState).
    */
    type ConsensusState: Async;

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
       [`HasIbcPacketTypes::IncomingPacket`](ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes::IncomingPacket)
    */
    type IncomingPacket: Async;

    /**
       Corresponds to
       [`HasIbcPacketTypes::OutgoingPacket`](ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes::OutgoingPacket)
    */
    type OutgoingPacket: Async;

    type CreateClientPayloadOptions: Async;

    type InitConnectionOptions: Async;

    type InitChannelOptions: Async;

    type CreateClientPayload: Async;

    type UpdateClientPayload: Async;

    type ConnectionOpenInitPayload: Async;

    type ConnectionOpenTryPayload: Async;

    type ConnectionOpenAckPayload: Async;

    type ConnectionOpenConfirmPayload: Async;

    type ChannelOpenTryPayload: Async;

    type ChannelOpenAckPayload: Async;

    type ChannelOpenConfirmPayload: Async;

    type ReceivePacketPayload: Async;

    type AckPacketPayload: Async;

    type TimeoutUnorderedPacketPayload: Async;

    type CreateClientEvent: Async;

    type ConnectionOpenInitEvent: Async;

    type ConnectionOpenTryEvent: Async;

    type ChannelOpenInitEvent: Async;

    type ChannelOpenTryEvent: Async;

    type SendPacketEvent: Async;

    /**
       Corresponds to
       [`HasWriteAcknowledgementEvent::WriteAcknowledgementEvent`](ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent::WriteAcknowledgementEvent).
    */
    type WriteAcknowledgementEvent: Async;
}

#[async_trait]
pub trait OfaChain: OfaChainTypes {
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;

    fn log_event<'a>(event: &'a Self::Event) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn log_incoming_packet<'a>(
        event: &'a Self::IncomingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn log_outgoing_packet<'a>(
        event: &'a Self::OutgoingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error>;

    fn estimate_message_size(message: &Self::Message) -> Result<usize, Self::Error>;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height;

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent>;

    fn extract_packet_from_send_packet_event(event: &Self::SendPacketEvent)
        -> Self::OutgoingPacket;

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket;

    fn try_extract_create_client_event(event: Self::Event) -> Option<Self::CreateClientEvent>;

    fn create_client_event_client_id(event: &Self::CreateClientEvent) -> &Self::ClientId;

    fn try_extract_connection_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenInitEvent>;

    fn client_state_latest_height(client_state: &Self::ClientState) -> &Self::Height;

    fn connection_open_init_event_connection_id(
        event: &Self::ConnectionOpenInitEvent,
    ) -> &Self::ConnectionId;

    fn try_extract_connection_open_try_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenTryEvent>;

    fn connection_open_try_event_connection_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> &Self::ConnectionId;

    fn try_extract_channel_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ChannelOpenInitEvent>;

    fn channel_open_init_event_channel_id(event: &Self::ChannelOpenInitEvent) -> &Self::ChannelId;

    fn try_extract_channel_open_try_event(event: Self::Event) -> Option<Self::ChannelOpenTryEvent>;

    fn channel_open_try_event_channel_id(event: &Self::ChannelOpenTryEvent) -> &Self::ChannelId;

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

    async fn query_write_acknowledgement_event(
        &self,
        packet: &Self::IncomingPacket,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;

    async fn build_create_client_payload(
        &self,
        create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<Self::CreateClientPayload, Self::Error>;

    async fn build_update_client_payload(
        &self,
        trusted_height: &Self::Height,
        target_height: &Self::Height,
        client_state: Self::ClientState,
    ) -> Result<Self::UpdateClientPayload, Self::Error>;

    async fn build_connection_open_init_payload(
        &self,
        client_state: &Self::ClientState,
    ) -> Result<Self::ConnectionOpenInitPayload, Self::Error>;

    async fn build_connection_open_try_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error>;

    async fn build_connection_open_ack_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error>;

    async fn build_connection_open_confirm_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error>;

    async fn build_channel_open_try_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Self::Error>;

    async fn build_channel_open_ack_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenAckPayload, Self::Error>;

    async fn build_channel_open_confirm_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenConfirmPayload, Self::Error>;

    async fn build_receive_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Self::ReceivePacketPayload, Self::Error>;

    async fn build_ack_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Self::AckPacketPayload, Self::Error>;

    async fn build_timeout_unordered_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Self::Error>;
}

#[async_trait]
pub trait OfaIbcChain<Counterparty>: OfaChain
where
    Counterparty: OfaChainTypes,
{
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

    fn counterparty_message_height_for_update_client(
        message: &Self::Message,
    ) -> Option<Counterparty::Height>;

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<Counterparty::ChainId, Self::Error>;

    async fn query_client_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Counterparty::ClientState, Self::Error>;

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Counterparty::Height,
    ) -> Result<Counterparty::ConsensusState, Self::Error>;

    async fn find_consensus_state_height_before(
        &self,
        client_id: &Self::ClientId,
        target_height: &Counterparty::Height,
    ) -> Result<Counterparty::Height, Self::Error>;

    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error>;

    /// Query the sequences of the packets that the chain has committed to be
    /// sent to the counterparty chain, of which the full packet relaying is not
    /// yet completed. Once the chain receives the ack from the counterparty
    /// chain, a given sequence should be removed from the packet commitment list.
    async fn query_packet_commitments(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error>;

    /// Given a list of counterparty commitment sequences,
    /// return a filtered list of sequences which the chain
    /// has not received the packet from the counterparty chain.
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<Vec<Counterparty::Sequence>, Self::Error>;

    /// Given a list of sequences, a channel and port will query a list of outgoing
    /// packets which have not been relayed.
    async fn query_send_packets_from_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Self::Sequence],
        // The height is given to query the packets from a specific height.
        // This height should be the same as the query height from the
        // `CanQueryPacketCommitments` made on the same chain.
        height: &Self::Height,
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error>;

    async fn build_receive_packet_message(
        &self,
        packet: &Self::IncomingPacket,
        payload: Counterparty::ReceivePacketPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_ack_packet_message(
        &self,
        packet: &Self::OutgoingPacket,
        payload: Counterparty::AckPacketPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_timeout_unordered_packet_message(
        &self,
        packet: &Self::OutgoingPacket,
        payload: Counterparty::TimeoutUnorderedPacketPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_create_client_message(
        &self,
        counterparty_payload: Counterparty::CreateClientPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_update_client_message(
        &self,
        client_id: &Self::ClientId,
        payload: Counterparty::UpdateClientPayload,
    ) -> Result<Vec<Self::Message>, Self::Error>;

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

    async fn build_channel_open_init_message(
        &self,
        port_id: &Self::PortId,
        counterparty_port_id: &Counterparty::PortId,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_channel_open_try_message(
        &self,
        port_id: &Self::PortId,
        counterparty_port_id: &Counterparty::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenTryPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_channel_open_ack_message(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenAckPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error>;
}
