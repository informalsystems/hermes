//! The following types are used for the OfaChainTypes implementation:
//! * For the Height a wrapper around a u128 referred to
//!   as MockHeight.
//! * For the Timestamp is a simple u128 representing milliseconds and is
//!   retrieved using a shared clock, MockClock.
//! * For the messages a simple enum MockMessage which allows to identify
//!   RecvPacket, AckPacket, TimeoutPacket and UpdateClient messages.
//! * The ConsensusState is a set of 4 HashSet used to store which messages
//!   have been sent, received, acknowledged and timed out.
//! * The ChainStatus is a ConsensusState with a Height and Timestamp.

use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use async_trait::async_trait;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::{
    ChainStatus, ChannelId, ClientId, ConsensusState, MockTimestamp, PortId, Sequence,
};
use crate::relayer_mock::base::types::chain::MockChainStatus;
use crate::relayer_mock::base::types::events::{Event, WriteAcknowledgementEvent};
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::packet::PacketKey;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};

use ibc_relayer_framework::base::one_for_all::presets::min::MinimalPreset;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

impl OfaChainTypes for MockChainContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Height = MockHeight;

    type Timestamp = MockTimestamp;

    type Message = MockMessage;

    type Event = Event;

    type ClientId = ClientId;

    type ConnectionId = String;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type WriteAcknowledgementEvent = WriteAcknowledgementEvent;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;
}

#[async_trait]
impl OfaBaseChain for MockChainContext {
    fn runtime(&self) -> &OfaRuntimeWrapper<MockRuntimeContext> {
        self.runtime()
    }

    fn runtime_error(e: TokioError) -> Self::Error {
        Error::tokio(e)
    }

    // Only single messages are sent by the Mock Chain
    fn estimate_message_size(_message: &Self::Message) -> Result<usize, Self::Error> {
        Ok(1)
    }

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp {
        &status.timestamp
    }

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event {
            Event::WriteAcknowledgment(h) => Some(WriteAcknowledgementEvent::new(h)),
            _ => None,
        }
    }

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Error> {
        self.process_messages(messages)
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        let height = self.get_current_height();
        let state = self.get_current_state();
        // Since the MockChain only updates manually, the Height is increased by
        // 1 everytime the chain status is queried, without changing its state.
        self.new_block()?;
        let time = self.runtime().runtime.get_time();
        Ok(MockChainStatus::from((height, time, state)))
    }
}

#[async_trait]
impl OfaIbcChain<MockChainContext> for MockChainContext {
    type IncomingPacket = PacketKey;

    type OutgoingPacket = PacketKey;

    fn incoming_packet_src_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.channel_id
    }

    fn incoming_packet_src_port(packet: &PacketKey) -> &PortId {
        &packet.channel_id
    }

    fn incoming_packet_dst_port(packet: &PacketKey) -> &PortId {
        &packet.port_id
    }

    fn incoming_packet_dst_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.channel_id
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
        &packet.channel_id
    }

    fn outgoing_packet_src_port(packet: &PacketKey) -> &PortId {
        &packet.channel_id
    }

    fn outgoing_packet_dst_port(packet: &PacketKey) -> &PortId {
        &packet.port_id
    }

    fn outgoing_packet_dst_channel_id(packet: &PacketKey) -> &ChannelId {
        &packet.channel_id
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

    fn counterparty_message_height(message: &Self::Message) -> Option<Self::Height> {
        match message {
            MockMessage::RecvPacket(h, _) => Some(h.clone()),
            MockMessage::AckPacket(h, _) => Some(h.clone()),
            MockMessage::TimeoutPacket(h, _) => Some(h.clone()),
            _ => None,
        }
    }

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Self::ConsensusState, Self::Error> {
        let client_consensus =
            self.query_consensus_state_at_height(client_id.to_string(), height.clone())?;
        Ok(client_consensus)
    }

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::Sequence,
    ) -> Result<bool, Self::Error> {
        let state = self.get_current_state();
        Ok(state.check_received(port_id, channel_id, sequence))
    }

    async fn query_write_ack_event(
        &self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
        _counterparty_channel_id: &ChannelId,
        _counterparty_port_id: &PortId,
        _sequence: &Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        todo!()
    }

    async fn build_receive_packet_message(
        &self,
        height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<MockMessage, Error> {
        // If the latest state of the source chain doesn't have the packet as sent, return an error.
        let state = self.get_current_state();
        if !state.check_sent(&packet.port_id, &packet.channel_id, &packet.sequence) {
            return Err(Error::receive_without_sent(
                self.name().to_string(),
                self.name().to_string(),
            ));
        }
        Ok(MockMessage::RecvPacket(height.clone(), packet.clone()))
    }
}
