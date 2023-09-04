//! The following types are used for the OfaChainTypes implementation:
//! * For the Height, a wrapper around a u128, referred to as MockHeight.
//! * For the Timestamp, a u128 representing milliseconds is retrieved
//!   using a shared clock, MockClock.
//! * For messages, an enum, MockMessage, which identifies
//!   RecvPacket, AckPacket, TimeoutPacket, and UpdateClient messages.
//! * The ConsensusState is a set of 4 HashSets used to store which messages
//!   have been sent, received, acknowledged, and timed out.
//! * The ChainStatus is a ConsensusState with a Height and a Timestamp.

use async_trait::async_trait;
use eyre::eyre;
use ibc_relayer_components::chain::traits::client::client_state::CanQueryClientState;
use ibc_relayer_components::chain::traits::components::message_sender::CanSendMessages;
use ibc_relayer_components::chain::traits::logs::event::CanLogChainEvent;
use ibc_relayer_components::chain::traits::logs::packet::CanLogChainPacket;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use ibc_relayer_components::chain::traits::message_builders::receive_packet::{
    CanBuildReceivePacketMessage, CanBuildReceivePacketPayload,
};
use ibc_relayer_components::chain::traits::message_builders::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, CanBuildTimeoutUnorderedPacketPayload,
};
use ibc_relayer_components::chain::traits::queries::consensus_state::CanQueryConsensusState;
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use ibc_relayer_components::chain::traits::queries::status::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::queries::write_ack::CanQueryWriteAcknowledgement;
use ibc_relayer_components::chain::traits::types::chain_id::{HasChainId, HasChainIdType};
use ibc_relayer_components::chain::traits::types::client_state::HasClientStateType;
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::height::{CanIncrementHeight, HasHeightType};
use ibc_relayer_components::chain::traits::types::ibc::{
    HasCounterpartyMessageHeight, HasIbcChainTypes,
};
use ibc_relayer_components::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::message::{
    CanEstimateMessageSize, HasMessageType,
};
use ibc_relayer_components::chain::traits::types::packet::{HasIbcPacketFields, HasIbcPacketTypes};
use ibc_relayer_components::chain::traits::types::packets::ack::HasAckPacketPayload;
use ibc_relayer_components::chain::traits::types::packets::receive::HasReceivePacketPayload;
use ibc_relayer_components::chain::traits::types::packets::timeout::HasTimeoutUnorderedPacketPayload;
use ibc_relayer_components::chain::traits::types::status::HasChainStatusType;
use ibc_relayer_components::chain::traits::types::timestamp::HasTimestampType;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::log::value::LogValue;

use crate::relayer_mock::base::error::{BaseError, Error};
use crate::relayer_mock::base::types::aliases::{
    ChainStatus, ChannelId, ClientId, ConsensusState, MockTimestamp, PortId, Sequence,
};
use crate::relayer_mock::base::types::chain::MockChainStatus;
use crate::relayer_mock::base::types::events::{Event, SendPacketEvent, WriteAcknowledgementEvent};
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;

impl HasErrorType for MockChainContext {
    type Error = Error;
}

impl HasRuntime for MockChainContext {
    type Runtime = MockRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }
}

impl HasLoggerType for MockChainContext {
    type Logger = TracingLogger;
}

impl HasHeightType for MockChainContext {
    type Height = MockHeight;
}

impl HasEventType for MockChainContext {
    type Event = Event;
}

impl HasTimestampType for MockChainContext {
    type Timestamp = MockTimestamp;
}

impl HasMessageType for MockChainContext {
    type Message = MockMessage;
}

impl HasChainIdType for MockChainContext {
    type ChainId = String;
}

impl HasIbcChainTypes<MockChainContext> for MockChainContext {
    type ClientId = ClientId;

    type ConnectionId = String;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;
}

impl HasIbcPacketTypes<MockChainContext> for MockChainContext {
    type IncomingPacket = PacketKey;

    type OutgoingPacket = PacketKey;
}

impl HasIbcPacketFields<MockChainContext> for MockChainContext {
    fn incoming_packet_src_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.src_channel_id
    }

    fn incoming_packet_src_port(packet: &PacketKey) -> &PortId {
        &packet.src_port_id
    }

    fn incoming_packet_dst_port(packet: &PacketKey) -> &PortId {
        &packet.dst_port_id
    }

    fn incoming_packet_dst_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.dst_channel_id
    }

    fn incoming_packet_sequence(packet: &PacketKey) -> &Sequence {
        &packet.sequence
    }

    fn incoming_packet_timeout_height(packet: &PacketKey) -> Option<&MockHeight> {
        Some(&packet.timeout_height)
    }

    fn incoming_packet_timeout_timestamp(packet: &PacketKey) -> &MockTimestamp {
        &packet.timeout_timestamp
    }

    fn outgoing_packet_src_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.src_channel_id
    }

    fn outgoing_packet_src_port(packet: &PacketKey) -> &PortId {
        &packet.src_port_id
    }

    fn outgoing_packet_dst_port(packet: &PacketKey) -> &PortId {
        &packet.dst_port_id
    }

    fn outgoing_packet_dst_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.dst_channel_id
    }

    fn outgoing_packet_sequence(packet: &PacketKey) -> &Sequence {
        &packet.sequence
    }

    fn outgoing_packet_timeout_height(packet: &PacketKey) -> Option<&MockHeight> {
        Some(&packet.timeout_height)
    }

    fn outgoing_packet_timeout_timestamp(packet: &PacketKey) -> &MockTimestamp {
        &packet.timeout_timestamp
    }
}

impl HasWriteAcknowledgementEvent<MockChainContext> for MockChainContext {
    type WriteAcknowledgementEvent = WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event {
            Event::WriteAcknowledgment(h) => Some(WriteAcknowledgementEvent::new(*h)),
            _ => None,
        }
    }
}

impl HasConsensusStateType<MockChainContext> for MockChainContext {
    type ConsensusState = ConsensusState;
}

impl HasClientStateType<MockChainContext> for MockChainContext {
    // TODO
    type ClientState = ();
}

impl HasChainStatusType for MockChainContext {
    type ChainStatus = ChainStatus;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp {
        &status.timestamp
    }
}

impl HasSendPacketEvent<MockChainContext> for MockChainContext {
    type SendPacketEvent = SendPacketEvent;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent> {
        match event {
            Event::SendPacket(send_packet_event) => Some(send_packet_event.clone()),
            _ => None,
        }
    }

    fn extract_packet_from_send_packet_event(
        event: &Self::SendPacketEvent,
    ) -> Self::OutgoingPacket {
        PacketKey::from(event.clone())
    }
}

impl HasLogger for MockChainContext {
    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }
}

impl CanLogChainEvent for MockChainContext {
    fn log_event<'a>(event: &Event) -> LogValue<'_> {
        LogValue::Debug(event)
    }
}

impl CanIncrementHeight for MockChainContext {
    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error> {
        Ok(height.increment())
    }
}

impl CanEstimateMessageSize for MockChainContext {
    fn estimate_message_size(_message: &Self::Message) -> Result<usize, Self::Error> {
        // Only single messages are sent by the Mock Chain
        Ok(1)
    }
}

impl HasChainId for MockChainContext {
    fn chain_id(&self) -> &Self::ChainId {
        &self.name
    }
}

#[async_trait]
impl CanSendMessages for MockChainContext {
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Error> {
        self.process_messages(messages)
    }
}

#[async_trait]
impl CanQueryChainStatus for MockChainContext {
    async fn query_chain_status(&self) -> Result<ChainStatus, Self::Error> {
        let height = self.get_current_height();
        let state = self.get_current_state();
        // Since the MockChain only updates manually, the Height is increased by
        // 1 everytime the chain status is queried, without changing its state.
        self.new_block()?;
        let time = self.runtime.get_time();
        Ok(MockChainStatus::from((height, time, state)))
    }
}

impl CanLogChainPacket<MockChainContext> for MockChainContext {
    fn log_incoming_packet(packet: &PacketKey) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn log_outgoing_packet(packet: &PacketKey) -> LogValue<'_> {
        LogValue::Display(packet)
    }
}

impl HasCounterpartyMessageHeight<MockChainContext> for MockChainContext {
    fn counterparty_message_height_for_update_client(message: &MockMessage) -> Option<MockHeight> {
        match message {
            MockMessage::RecvPacket(h, _) => Some(h.increment()),
            MockMessage::AckPacket(h, _) => Some(h.increment()),
            MockMessage::TimeoutPacket(h, _) => Some(h.increment()),
            _ => None,
        }
    }
}

#[async_trait]
impl CanQueryConsensusState<MockChainContext> for MockChainContext {
    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &MockHeight,
    ) -> Result<ConsensusState, Self::Error> {
        let client_consensus =
            self.query_consensus_state_at_height(client_id.to_string(), *height)?;
        Ok(client_consensus)
    }
}

#[async_trait]
impl CanQueryClientState<MockChainContext> for MockChainContext {
    async fn query_client_state(&self, _client_id: &Self::ClientId) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[async_trait]
impl CanQueryReceivedPacket<MockChainContext> for MockChainContext {
    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::Sequence,
    ) -> Result<bool, Self::Error> {
        let state = self.get_current_state();
        Ok(state.check_received((port_id.clone(), channel_id.clone(), *sequence)))
    }
}

#[async_trait]
impl CanQueryWriteAcknowledgement<MockChainContext> for MockChainContext {
    async fn query_write_acknowledgement_event(
        &self,
        packet: &PacketKey,
    ) -> Result<Option<WriteAcknowledgementEvent>, Error> {
        let received = self.get_received_packet_information(
            packet.dst_port_id.clone(),
            packet.dst_channel_id.clone(),
            packet.sequence,
        );

        if let Some((packet2, height)) = received {
            if &packet2 == packet {
                Ok(Some(WriteAcknowledgementEvent::new(height)))
            } else {
                Err(BaseError::generic(eyre!(
                    "mismatch between packet in state {} and packet: {}",
                    packet2,
                    packet
                ))
                .into())
            }
        } else {
            Ok(None)
        }
    }
}

impl HasReceivePacketPayload<MockChainContext> for MockChainContext {
    type ReceivePacketPayload = MockMessage;
}

#[async_trait]
impl CanBuildReceivePacketPayload<MockChainContext> for MockChainContext {
    async fn build_receive_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<MockMessage, Error> {
        // If the latest state of the source chain doesn't have the packet as sent, return an error.
        let state = self.get_current_state();
        if !state.check_sent((
            packet.src_port_id.clone(),
            packet.src_channel_id.clone(),
            packet.sequence,
        )) {
            return Err(BaseError::receive_without_sent(
                self.name().to_string(),
                packet.src_channel_id.to_string(),
            )
            .into());
        }
        Ok(MockMessage::RecvPacket(*height, packet.clone()))
    }
}

#[async_trait]
impl CanBuildReceivePacketMessage<MockChainContext> for MockChainContext {
    async fn build_receive_packet_message(
        &self,
        _packet: &PacketKey,
        payload: MockMessage,
    ) -> Result<MockMessage, Error> {
        Ok(payload)
    }
}

impl HasAckPacketPayload<MockChainContext> for MockChainContext {
    type AckPacketPayload = MockMessage;
}

#[async_trait]
impl CanBuildAckPacketPayload<MockChainContext> for MockChainContext {
    async fn build_ack_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &MockHeight,
        packet: &PacketKey,
        _ack: &WriteAcknowledgementEvent,
    ) -> Result<MockMessage, Error> {
        // If the latest state of the destination chain doesn't have the packet as received, return an error.
        let state = self.get_current_state();

        if !state.check_received((
            packet.dst_port_id.clone(),
            packet.dst_channel_id.clone(),
            packet.sequence,
        )) {
            return Err(BaseError::acknowledgment_without_received(
                self.name().to_string(),
                packet.dst_channel_id.to_string(),
            )
            .into());
        }

        Ok(MockMessage::AckPacket(*height, packet.clone()))
    }
}

#[async_trait]
impl CanBuildAckPacketMessage<MockChainContext> for MockChainContext {
    async fn build_ack_packet_message(
        &self,
        _packet: &PacketKey,
        payload: MockMessage,
    ) -> Result<MockMessage, Error> {
        Ok(payload)
    }
}

impl HasTimeoutUnorderedPacketPayload<MockChainContext> for MockChainContext {
    type TimeoutUnorderedPacketPayload = MockMessage;
}

#[async_trait]
impl CanBuildTimeoutUnorderedPacketPayload<MockChainContext> for MockChainContext {
    async fn build_timeout_unordered_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<MockMessage, Error> {
        let state = self.get_current_state();
        let current_timestamp = self.runtime.get_time();

        if !state.check_timeout(packet.clone(), *height, current_timestamp) {
            return Err(BaseError::timeout_without_sent(
                self.name().to_string(),
                packet.src_channel_id.to_string(),
            )
            .into());
        }

        Ok(MockMessage::TimeoutPacket(*height, packet.clone()))
    }
}

#[async_trait]
impl CanBuildTimeoutUnorderedPacketMessage<MockChainContext> for MockChainContext {
    async fn build_timeout_unordered_packet_message(
        &self,
        _packet: &PacketKey,
        payload: MockMessage,
    ) -> Result<MockMessage, Error> {
        Ok(payload)
    }
}
