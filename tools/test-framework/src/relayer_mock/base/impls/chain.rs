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

    type RawMessage = Vec<u8>;

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
        unimplemented!()
    }

    fn encode_raw_message(
        _message: &Self::Message,
        _signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error> {
        unimplemented!()
    }

    fn estimate_message_len(_message: &Self::Message) -> Result<usize, Self::Error> {
        unimplemented!()
    }

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(_status: &Self::ChainStatus) -> &Self::Timestamp {
        unimplemented!()
    }

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event {
            Event::RecvPacket(_) => Some(WriteAcknowledgementEvent{}),
            _ => None,
        }
    }

    async fn send_messages(&self, messages: Vec<MockMessage>) -> Result<Vec<Vec<Event>>, Error> {
        let mut res = vec![];
        for m in messages {
            if let MockMessage::SendPacket(h) = m {
                res.push(Event::RecvPacket(h));
            }
        }
        Ok(vec![res])
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Ok(ChainStatus::default())
    }
}

#[async_trait]
impl OfaIbcChain<MockChainContext> for MockChainContext {
    fn counterparty_message_height(message: &Self::Message) -> Option<u128> {
        match message {
            MockMessage::SendPacket(h) => Some(*h),
            MockMessage::AckPacket(h) => Some(*h),
            MockMessage::TimeoutPacket(h) => Some(*h),
            _ => None,
        }
    }

    async fn query_consensus_state(
        &self,
        client_id: &String,
        height: &u128,
    ) -> Result<ConsensusState, Self::Error> {
        let res = self.query_state(Height::from(*height));
        if let Some(_state) = res {
            Ok(ConsensusState{ })
        } else {
            Err(Error::no_consensus_state(client_id.clone()))
        }
    }

    async fn is_packet_received(
        &self,
        port_id: &String,
        channel_id: &String,
        sequence: &u128,
    ) -> Result<bool, Self::Error> {
        if let Some(height) = self.get_latest_height() {
            if let Some(state) = self.query_state(height.clone()) {
                return Ok(state.check_received(port_id, channel_id, sequence));
            }
            return Err(Error::no_height_state(height.0));
        }
        return Err(Error::no_height(self.name().to_string()));
    }
}
