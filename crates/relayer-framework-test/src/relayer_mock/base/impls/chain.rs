//! The following types are used for the OfaChainTypes implementation:
//! * For the Height, a wrapper around a u128, referred to as MockHeight.
//! * For the Timestamp, a u128 representing milliseconds is retrieved
//!   using a shared clock, MockClock.
//! * For messages, an enum, MockMessage, which identifies
//!   RecvPacket, AckPacket, TimeoutPacket, and UpdateClient messages.
//! * The ConsensusState is a set of 4 HashSets used to store which messages
//!   have been sent, received, acknowledged, and timed out.
//! * The ChainStatus is a ConsensusState with a Height and a Timestamp.

use alloc::sync::Arc;
use async_trait::async_trait;
use eyre::eyre;

use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};
use ibc_relayer_framework::base::runtime::traits::subscription::Subscription;

use ibc_relayer_framework::base::one_for_all::presets::min::MinimalPreset;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

use crate::relayer_mock::base::error::Error;
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

impl OfaChainTypes for MockChainContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Height = MockHeight;

    type Timestamp = MockTimestamp;

    type Message = MockMessage;

    type Event = Event;

    type ChainId = String;

    type ClientId = ClientId;

    type ConnectionId = String;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type WriteAcknowledgementEvent = WriteAcknowledgementEvent;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;

    type SendPacketEvent = SendPacketEvent;
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
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event {
            Event::WriteAcknowledgment(h) => Some(WriteAcknowledgementEvent::new(*h)),
            _ => None,
        }
    }

    fn chain_id(&self) -> &Self::ChainId {
        &self.name
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

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>> {
        todo!()
    }
}

#[async_trait]
impl OfaIbcChain<MockChainContext> for MockChainContext {
    type IncomingPacket = PacketKey;

    type OutgoingPacket = PacketKey;

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

    fn counterparty_message_height(message: &Self::Message) -> Option<Self::Height> {
        match message {
            MockMessage::RecvPacket(h, _) => Some(*h),
            MockMessage::AckPacket(h, _) => Some(*h),
            MockMessage::TimeoutPacket(h, _) => Some(*h),
            _ => None,
        }
    }

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

    fn extract_packet_from_write_acknowledgement_event(
        _ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket {
        todo!()
    }

    async fn query_chain_id_from_channel_id(
        &self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
    ) -> Result<String, Self::Error> {
        todo!()
    }

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Self::ConsensusState, Self::Error> {
        let client_consensus =
            self.query_consensus_state_at_height(client_id.to_string(), *height)?;
        Ok(client_consensus)
    }

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::Sequence,
    ) -> Result<bool, Self::Error> {
        let state = self.get_current_state();
        Ok(state.check_received((port_id.clone(), channel_id.clone(), *sequence)))
    }

    async fn query_write_ack_event(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_port_id: &PortId,
        sequence: &Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        let received = self.get_received_packet_information(
            counterparty_port_id.clone(),
            counterparty_channel_id.clone(),
            *sequence,
        );
        if let Some((packet, height)) = received {
            if &packet.src_channel_id == channel_id
                && &packet.src_port_id == port_id
                && &packet.dst_channel_id == counterparty_channel_id
                && &packet.dst_port_id == port_id
                && &packet.sequence == sequence
            {
                Ok(Some(WriteAcknowledgementEvent::new(height)))
            } else {
                Err(Error::generic(eyre!("mismatch between packet in state {} and query parameters: channel_id: {}, port_id: {}, counterparty_channel_id: {}, counterparty_port_id: {}, sequence: {}", packet, channel_id, port_id, counterparty_channel_id, counterparty_port_id, sequence)))
            }
        } else {
            Ok(None)
        }
    }

    async fn build_receive_packet_message(
        &self,
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
            return Err(Error::receive_without_sent(
                self.name().to_string(),
                packet.src_channel_id.to_string(),
            ));
        }
        Ok(MockMessage::RecvPacket(*height, packet.clone()))
    }

    async fn build_ack_packet_message(
        &self,
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
            return Err(Error::acknowledgment_without_received(
                self.name().to_string(),
                packet.dst_channel_id.to_string(),
            ));
        }

        Ok(MockMessage::AckPacket(*height, packet.clone()))
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        height: &MockHeight,
        packet: &PacketKey,
    ) -> Result<MockMessage, Error> {
        let state = self.get_current_state();
        let runtime = &self.runtime().runtime;
        let current_timestamp = runtime.get_time();

        if !state.check_timeout(packet.clone(), *height, current_timestamp) {
            return Err(Error::timeout_without_sent(
                self.name().to_string(),
                packet.src_channel_id.to_string(),
            ));
        }

        Ok(MockMessage::TimeoutPacket(*height, packet.clone()))
    }
}
