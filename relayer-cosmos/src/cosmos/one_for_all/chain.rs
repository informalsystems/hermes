use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc::core::ics02_client::client_consensus::AnyConsensusState;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::endpoint::ChainStatus as CosmosChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer_framework::one_for_all::traits::chain::OfaChain;
use ibc_relayer_framework::one_for_all::traits::components::default::DefaultComponents;
use prost::Message as _;
use tendermint::abci::responses::Event;

use crate::cosmos::context::chain::{CosmosChainContext, WriteAcknowledgementEvent};
use crate::cosmos::context::runtime::CosmosRuntime;
use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

#[async_trait]
impl<Handle> OfaChain for CosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    type Components = DefaultComponents;

    type Error = Error;

    type Runtime = CosmosRuntime;

    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Signer = Signer;

    type RawMessage = Any;

    type Event = Event;

    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type WriteAcknowledgementEvent = WriteAcknowledgementEvent;

    type ConsensusState = ConsensusState;

    type ChainStatus = CosmosChainStatus;

    type CounterpartySequence = Sequence;

    type CounterpartyHeight = Height;

    type CounterpartyConsensusState = ConsensusState;

    fn encode_raw_message(
        message: &Self::Message,
        signer: &Self::Signer,
    ) -> Result<Self::RawMessage, Self::Error> {
        (message.to_protobuf_fn)(signer).map_err(Error::encode)
    }

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        let raw = (message.to_protobuf_fn)(&Signer::dummy()).map_err(Error::encode)?;

        Ok(raw.encoded_len())
    }

    fn source_message_height(message: &Self::Message) -> Option<Self::CounterpartyHeight> {
        message.source_height
    }

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp {
        &status.timestamp
    }

    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        let signer = &self.signer;

        let raw_messages = messages
            .into_iter()
            .map(|message| Self::encode_raw_message(&message, signer))
            .collect::<Result<Vec<_>, _>>()?;

        let events = simple_send_tx(&self.tx_config, &self.key_entry, raw_messages)
            .await
            .map_err(Error::relayer)?;

        Ok(events)
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        let status = self
            .handle
            .query_application_status()
            .map_err(Error::relayer)?;

        Ok(status)
    }

    async fn query_consensus_state(
        &self,
        client_id: &Self::ClientId,
        height: &Self::CounterpartyHeight,
    ) -> Result<Self::CounterpartyConsensusState, Self::Error> {
        let (any_consensus_state, _) = self
            .handle
            .query_consensus_state(
                QueryConsensusStateRequest {
                    client_id: client_id.clone(),
                    consensus_height: *height,
                    query_height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(Error::relayer)?;

        match any_consensus_state {
            AnyConsensusState::Tendermint(consensus_state) => Ok(consensus_state),
            _ => Err(Error::mismatch_consensus_state()),
        }
    }

    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::CounterpartySequence,
    ) -> Result<bool, Self::Error> {
        let unreceived_packet = self
            .handle
            .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                port_id: port_id.clone(),
                channel_id: channel_id.clone(),
                packet_commitment_sequences: vec![*sequence],
            })
            .map_err(Error::relayer)?;

        let is_packet_received = unreceived_packet.is_empty();

        Ok(is_packet_received)
    }
}
