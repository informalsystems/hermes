use async_trait::async_trait;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, Qualified, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer::link::packet_events::query_write_ack_events;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_framework::base::chain::traits::message_sender::CanSendMessages;
use ibc_relayer_framework::base::one_for_all::traits::chain::{
    OfaBaseChain, OfaChainTypes, OfaIbcChain,
};
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::WriteAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::PacketMsgType;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::events::{IbcEvent, IbcEventType};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;
use prost::Message as _;
use tendermint::abci::Event;

use crate::base::error::Error;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::message::CosmosIbcMessage;

impl<Chain> OfaChainTypes for CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    type Preset = Chain::Preset;

    type Error = Error;

    type Runtime = TokioRuntimeContext;

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
    fn runtime_error(e: TokioError) -> Error {
        Error::tokio(e)
    }

    fn estimate_message_size(message: &CosmosIbcMessage) -> Result<usize, Error> {
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

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        self.tx_context.send_messages(messages).await
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
    type IncomingPacket = Packet;

    type OutgoingPacket = Packet;

    fn incoming_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        &packet.source_channel
    }

    fn incoming_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        &packet.destination_channel
    }

    fn incoming_packet_src_port(packet: &Packet) -> &PortId {
        &packet.source_port
    }

    fn incoming_packet_dst_port(packet: &Packet) -> &PortId {
        &packet.destination_port
    }

    fn incoming_packet_sequence(packet: &Packet) -> &Sequence {
        &packet.sequence
    }

    fn incoming_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        match &packet.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn incoming_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        &packet.timeout_timestamp
    }

    fn outgoing_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        &packet.source_channel
    }

    fn outgoing_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        &packet.destination_channel
    }

    fn outgoing_packet_src_port(packet: &Packet) -> &PortId {
        &packet.source_port
    }

    fn outgoing_packet_dst_port(packet: &Packet) -> &PortId {
        &packet.destination_port
    }

    fn outgoing_packet_sequence(packet: &Packet) -> &Sequence {
        &packet.sequence
    }

    fn outgoing_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        match &packet.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn outgoing_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        &packet.timeout_timestamp
    }

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
        let status = self.query_chain_status().await?;
        let chain_handle = self.chain.chain_handle();
        let src_query_height =
            Qualified::Equal(*CosmosChainWrapper::<Chain>::chain_status_height(&status));
        let path_ident = PathIdentifiers {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            counterparty_port_id: counterparty_port_id.clone(),
            counterparty_channel_id: counterparty_channel_id.clone(),
        };

        let ibc_events =
            query_write_ack_events(chain_handle, &path_ident, &[*sequence], src_query_height)
                .map_err(Error::relayer)?;

        let write_ack = ibc_events.into_iter().find_map(|event_with_height| {
            let event = event_with_height.event;

            if let IbcEvent::WriteAcknowledgement(write_ack) = event {
                Some(write_ack)
            } else {
                None
            }
        });

        Ok(write_ack)
    }

    /// Construct a receive packet to be sent to a destination Cosmos
    /// chain from a source Cosmos chain.
    async fn build_receive_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let proofs = self
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::Recv,
                &packet.source_port,
                &packet.source_channel,
                packet.sequence,
                *height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();

        let message = CosmosIbcMessage::new(Some(*height), move |signer| {
            Ok(MsgRecvPacket::new(packet.clone(), proofs.clone(), signer.clone()).to_any())
        });

        Ok(message)
    }

    /// Construct an acknowledgement packet to be sent from a Cosmos
    /// chain that successfully received a packet from another Cosmos
    /// chain.
    async fn build_ack_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
        ack: &WriteAcknowledgementEvent,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let proofs = self
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::Ack,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                *height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();
        let ack = ack.clone;

        let message = CosmosIbcMessage::new(Some(*height), move |signer| {
            Ok(MsgAcknowledgement::new(
                packet.clone(),
                ack.clone().into(),
                proofs.clone(),
                signer.clone(),
            )
            .to_any())
        });

        Ok(message)
    }

    /// Construct a timeout packet message to be sent between Cosmos chains
    /// over an unordered Cosmos channel in the event that a packet orginating
    /// from a source chain was not received.
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let proofs = self
            .chain
            .chain_handle()
            .build_packet_proofs(
                PacketMsgType::TimeoutUnordered,
                &packet.destination_port,
                &packet.destination_channel,
                packet.sequence,
                *height,
            )
            .map_err(Error::relayer)?;

        let packet = packet.clone();

        let message = CosmosIbcMessage::new(Some(*height), move |signer| {
            Ok(MsgTimeout::new(
                packet.clone(),
                packet.sequence,
                proofs.clone(),
                signer.clone(),
            )
            .to_any())
        });

        Ok(message)
    }
}
