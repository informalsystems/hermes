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
use crate::relayer_mock::base::types::runtime::MockRuntimeContext;
use crate::relayer_mock::contexts::chain::MockChainContext;

impl OfaChainTypes for MockChainContext {
    type Preset = MinimalPreset;

    type Error = Error;

    type Runtime = MockRuntimeContext;

    type Height = u128;

    type Timestamp = Height;

    type Message = String;

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

    // For this Mock Chain, a Write Acknowledgement Event is extracted when
    // an Receive Packet Event, which is defined by a packet with the format:
    // `<channel_id>/<port_id>:recv-<packet_sequence>/<chain_height-packet_heigh>`
    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event.event_type.as_str() {
            t if t.contains("recv") => Some(WriteAcknowledgementEvent {}),
            _ => None,
        }
    }

    async fn send_messages(&self, messages: Vec<String>) -> Result<Vec<Vec<Event>>, Error> {
        let mut res = vec![];
        for m in messages {
            res.push(Event::new(m));
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
        let height_block = message.rsplit_once(':');
        if let Some((_, h1)) = height_block {
            let extract_height = h1.rsplit_once('-');
            if let Some((_, _h2)) = extract_height {
                return None;
            } else {
                return None;
            }
        }
        None
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

    // The Mock Chain assumes packets are never received.
    // This is temporary
    async fn is_packet_received(
        &self,
        _port_id: &String,
        _channel_id: &String,
        _sequence: &u128,
    ) -> Result<bool, Self::Error> {
        Ok(false)
    }
}
