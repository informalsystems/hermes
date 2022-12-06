use async_trait::async_trait;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, Qualified, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer::link::packet_events::query_write_ack_events;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::events::IbcEventType;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use prost::Message as _;
use tendermint::abci::Event;

use crate::base::error::Error;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::message::CosmosIbcMessage;
use crate::base::types::runtime::CosmosRuntimeContext;

impl<Chain> OfaChainTypes for CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    type Preset = Chain::Preset;

    type Error = Error;

    type Runtime = CosmosRuntimeContext;

    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = Event;

    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type WriteAcknowledgementEvent = WriteAcknowledgement;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;
}

#[async_trait]
impl<Chain> OfaBaseChain for CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
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
        if let IbcEventType::WriteAck = event.kind.parse().ok()? {
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
            .map(|message| (message.to_protobuf_fn)(signer).map_err(Error::encode))
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
}

#[async_trait]
impl<Chain, Counterparty> OfaIbcChain<CosmosChainWrapper<Counterparty>>
    for CosmosChainWrapper<Chain>
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

    async fn query_write_ack_event(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &<CosmosChainWrapper<Counterparty> as OfaChainTypes>::ChannelId,
        counterparty_port_id: &<CosmosChainWrapper<Counterparty> as OfaChainTypes>::PortId,
        sequence: &<CosmosChainWrapper<Counterparty> as OfaChainTypes>::Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        let chain_handle = self.chain.chain_handle();
        let status = self.query_chain_status().await?;
        let path_ident = PathIdentifiers {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            counterparty_port_id: counterparty_port_id.clone(),
            counterparty_channel_id: counterparty_channel_id.clone(),
        };
        let src_query_height =
            Qualified::Equal(*CosmosChainWrapper::<Chain>::chain_status_height(&status));
        // Call the `query_write_ack_events` method to fetch a Vec<IbcEventWithHeight>
        let ibc_events =
            query_write_ack_events(chain_handle, &path_ident, &[*sequence], src_query_height);
        // Search through the vec of events to find the `WriteAcknowledgement` event
        // Return the event if one is found
        todo!()
    }
}
