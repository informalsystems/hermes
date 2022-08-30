use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc::core::ics04_channel::events::WriteAcknowledgement;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::events::IbcEventType;
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer_framework::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
use prost::Message as _;
use tendermint::abci::responses::Event;

use crate::cosmos::core::error::Error;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::message::CosmosIbcMessage;
use crate::cosmos::core::types::runtime::CosmosRuntimeContext;
use crate::cosmos::core::types::telemetry::CosmosTelemetry;

#[async_trait]
impl<Chain> OfaChain for CosmosChainContext<Chain>
where
    Chain: CosmosChain,
{
    type Components = Chain::Components;

    type Error = Error;

    type Runtime = CosmosRuntimeContext;

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

    type WriteAcknowledgementEvent = WriteAcknowledgement;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;

    type Telemetry = CosmosTelemetry;

    fn encode_raw_message(message: &CosmosIbcMessage, signer: &Signer) -> Result<Any, Error> {
        (message.to_protobuf_fn)(signer).map_err(Error::encode)
    }

    fn estimate_message_len(message: &CosmosIbcMessage) -> Result<usize, Error> {
        let raw = (message.to_protobuf_fn)(&Signer::dummy()).map_err(Error::encode)?;

        Ok(raw.encoded_len())
    }

    fn chain_status_height(status: &ChainStatus) -> &Height {
        &status.height
    }

    fn chain_status_timestamp(status: &ChainStatus) -> &Timestamp {
        &status.timestamp
    }

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        if let IbcEventType::WriteAck = event.type_str.parse().ok()? {
            let (packet, write_ack) = extract_packet_and_write_ack_from_tx(&event).ok()?;

            let ack = WriteAcknowledgement {
                packet,
                ack: write_ack,
            };

            Some(ack)
        } else {
            None
        }
    }

    fn runtime(&self) -> &OfaRuntimeContext<CosmosRuntimeContext> {
        &self.runtime
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        let signer = self.chain.signer();

        let raw_messages = messages
            .into_iter()
            .map(|message| Self::encode_raw_message(&message, signer))
            .collect::<Result<Vec<_>, _>>()?;

        let events = simple_send_tx(self.chain.tx_config(), self.chain.key_entry(), raw_messages)
            .await
            .map_err(Error::relayer)?;

        Ok(events)
    }

    async fn query_chain_status(&self) -> Result<ChainStatus, Self::Error> {
        let status = self
            .chain
            .chain_handle()
            .query_application_status()
            .map_err(Error::relayer)?;

        Ok(status)
    }

    fn telemetry(&self) -> &CosmosTelemetry {
        &self.telemetry
    }
}

#[async_trait]
impl<Chain, Counterparty> OfaIbcChain<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: CosmosChain,
    Counterparty: CosmosChain,
{
    fn counterparty_message_height(message: &CosmosIbcMessage) -> Option<Height> {
        message.source_height
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<ConsensusState, Error> {
        let (any_consensus_state, _) = self
            .chain
            .chain_handle()
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
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Error> {
        let unreceived_packet = self
            .chain
            .chain_handle()
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
