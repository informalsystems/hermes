use async_trait::async_trait;

use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::presets::MinimalPreset;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::chain::{ChainStatus, ConsensusState};
use crate::relayer_mock::base::types::events::{Event, WriteAcknowledgementEvent};
use crate::relayer_mock::base::types::height::Height;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;

impl OfaChainTypes for MockChainContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Height = u128;

    type Timestamp = Height;

    type Message = MockMessage;

    type Signer = u128;

    type RawMessage = String;

    type Event = Event;

    type ClientId = String;

    type ConnectionId = String;

    type ChannelId = String;

    type PortId = String;

    type Sequence = u128;

    type WriteAcknowledgementEvent = WriteAcknowledgementEvent;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;
}

#[async_trait]
impl OfaBaseChain for MockChainContext {
    fn runtime(&self) -> &OfaRuntimeContext<MockRuntimeContext> {
        self.runtime()
    }

    fn encode_raw_message(
        message: &Self::Message,
        _signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error> {
        Ok(message.to_string())
    }

    // Only single messages are sent by the Mock Chain
    fn estimate_message_len(_message: &Self::Message) -> Result<usize, Self::Error> {
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
            Event::RecvPacket(_) => Some(WriteAcknowledgementEvent {}),
            _ => None,
        }
    }

    /// If the message is a `SendPacket`, update the received packets,
    /// and add a `RecvPacket` event to the returned array of events.
    /// If the message is an `AckPacket`, update the received acknowledgment
    /// packets.
    /// If the message is an `UpdateClient` update the consensus state.
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Error> {
        let mut res = vec![];
        for m in messages {
            match m {
                MockMessage::SendPacket(_, h, p) => {
                    self.receive_packet(p);
                    res.push(Event::RecvPacket(h));
                }
                MockMessage::AckPacket(_, p) => {
                    self.acknowledge_packet(p);
                }
                MockMessage::UpdateClient(h) => {
                    self.insert_consensus_state(Height(h));
                }
                _ => {}
            }
        }
        Ok(vec![res])
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        if let Some(h) = self.get_latest_height() {
            return Ok(ChainStatus::new(h.0, h));
        }
        return Err(Error::no_height(self.name().clone()));
    }
}

#[async_trait]
impl OfaIbcChain<MockChainContext> for MockChainContext {
    fn counterparty_message_height(message: &Self::Message) -> Option<Self::Height> {
        match message {
            MockMessage::SendPacket(_, h, _) => Some(*h),
            MockMessage::AckPacket(h, _) => Some(*h),
            MockMessage::TimeoutPacket(h, _) => Some(*h),
            _ => None,
        }
    }

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Self::ConsensusState, Self::Error> {
        let res = self.query_consensus_state(Height::from(*height));
        if res.is_some() {
            Ok(ConsensusState {})
        } else {
            Err(Error::no_consensus_state(client_id.to_string()))
        }
    }

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::Sequence,
    ) -> Result<bool, Self::Error> {
        match self.get_latest_height() {
            Some(height) => {
                if let Some(state) = self.query_state(height.clone()) {
                    return Ok(state.check_received(port_id, channel_id, sequence));
                }
                return Err(Error::no_height_state(height.0));
            }
            None => Ok(false),
        }
    }
}
