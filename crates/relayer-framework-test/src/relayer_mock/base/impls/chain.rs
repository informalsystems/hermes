//! The following types are used for the OfaChainTypes implementation:
//! * For the Height and Timestamp a wrapper around a u128 referred to
//!   as MockHeight. The MockChain does not require a precise timestamp
//!   such as Duration.
//! * For the messages a simple enum MockMessage which allows to identify
//!   RecvPacket, AckPacket, TimeoutPacket and UpdateClient messages.
//! * The ConsensusState is a set of 3 HashSet used to store which messages
//!   have been sent, received and acknowledged.
//! * The ChainStatus is a ConsensusState with a Height and Timestamp.

use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use async_trait::async_trait;
use eyre::eyre;
use std::vec;

use crate::relayer_mock::base::error::Error;
use crate::relayer_mock::base::types::aliases::{
    ChainStatus, ChannelId, ClientId, ConsensusState, PortId, Sequence,
};
use crate::relayer_mock::base::types::chain::MockChainStatus;
use crate::relayer_mock::base::types::events::{Event, WriteAcknowledgementEvent};
use crate::relayer_mock::base::types::height::Height as MockHeight;
use crate::relayer_mock::base::types::message::Message as MockMessage;
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;
use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_framework::common::one_for_all::presets::MinimalPreset;

impl OfaChainTypes for MockChainContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Height = MockHeight;

    type Timestamp = MockHeight;

    type Message = MockMessage;

    type Signer = u128;

    type RawMessage = String;

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
            Event::WriteAcknowledgment(h) => Some(WriteAcknowledgementEvent::new(h)),
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
                MockMessage::RecvPacket(receiver, h, p) => {
                    let client_consensus =
                        self.query_client_state_at_height(receiver.clone(), h.clone())?;
                    let state = client_consensus.get(&h).unwrap();
                    if !state.check_sent(&p.port_id, &p.channel_id, &p.sequence) {
                        return Err(Error::generic(eyre!("chain `{}` got a RecvPacket, but client `{}` state doesn't have the packet as sent", self.name(), receiver)));
                    }
                    // Check that the packet is not timed out. Current height < packet timeout height.
                    self.receive_packet(p)?;
                    res.push(vec![Event::WriteAcknowledgment(h)]);
                }
                MockMessage::AckPacket(receiver, h, p) => {
                    let client_consensus =
                        self.query_client_state_at_height(receiver.clone(), h.clone())?;
                    let state = client_consensus.get(&h).unwrap();
                    if !state.check_received(&p.port_id, &p.channel_id, &p.sequence) {
                        return Err(Error::generic(eyre!("chain `{}` got a AckPacket, but client `{}` state doesn't have the packet as received", self.name(), receiver)));
                    }
                    self.acknowledge_packet(p)?;
                    res.push(vec![]);
                }
                MockMessage::UpdateClient(receiver, h, s) => {
                    self.insert_client_state(receiver, h, s)?;
                    res.push(vec![]);
                }
                _ => {}
            }
        }
        Ok(res)
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        let height = self.get_latest_height();
        let state = self.get_current_state();
        // Since the MockChain only updates manually, the Height is increased by
        // 1 everytime the chain status is queried, without changing its state.
        self.new_block()?;
        Ok(MockChainStatus::from((height, state)))
    }
}

#[async_trait]
impl OfaIbcChain<MockChainContext> for MockChainContext {
    fn counterparty_message_height(message: &Self::Message) -> Option<Self::Height> {
        match message {
            MockMessage::RecvPacket(_, h, _) => Some(h.clone()),
            MockMessage::AckPacket(_, h, _) => Some(h.clone()),
            MockMessage::TimeoutPacket(_, h, _) => Some(h.clone()),
            _ => None,
        }
    }

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Self::ConsensusState, Self::Error> {
        let client_consensus =
            self.query_client_state_at_height(client_id.to_string(), height.clone())?;
        let state = client_consensus.get(height);
        if let Some(state) = state {
            return Ok(state.clone());
        }
        Err(Error::no_consensus_state(client_id.to_string()))
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
}
