use alloc::sync::Arc;

use async_trait::async_trait;
use ibc_relayer::chain::counterparty::counterparty_chain_from_channel;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, Qualified, QueryConsensusStateRequest, QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer::link::packet_events::query_write_ack_events;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_all_in_one::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_components::chain::traits::message_sender::CanSendMessages;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_runtime::tokio::logger::value::LogValue;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc_relayer_types::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::recv_packet::MsgRecvPacket;
use ibc_relayer_types::core::ics04_channel::msgs::timeout::MsgTimeout;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::PacketMsgType;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::events::{IbcEvent, IbcEventType};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;
use prost::Message as _;
use tendermint::abci::Event as AbciEvent;

use crate::contexts::chain::CosmosChain;
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;
use crate::types::telemetry::CosmosTelemetry;

#[async_trait]
impl<Chain> OfaChain for CosmosChain<Chain>
where
    Chain: ChainHandle,
{
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type Telemetry = CosmosTelemetry;

    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = Arc<AbciEvent>;

    type ChainId = ChainId;

    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type WriteAcknowledgementEvent = WriteAcknowledgement;

    type ConsensusState = ConsensusState;

    type ChainStatus = ChainStatus;

    type SendPacketEvent = SendPacket;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        BaseError::tokio(e).into()
    }

    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }

    fn log_event(event: &Arc<AbciEvent>) -> LogValue<'_> {
        LogValue::Debug(event)
    }

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        &self.telemetry
    }

    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error> {
        Ok(height.increment())
    }

    fn estimate_message_size(message: &CosmosIbcMessage) -> Result<usize, Error> {
        let raw = (message.to_protobuf_fn)(&Signer::dummy()).map_err(BaseError::encode)?;

        Ok(raw.encoded_len())
    }

    fn chain_status_height(status: &ChainStatus) -> &Height {
        &status.height
    }

    fn chain_status_timestamp(status: &ChainStatus) -> &Timestamp {
        &status.timestamp
    }

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        if let IbcEventType::WriteAck = event.kind.parse().ok()? {
            let (packet, write_ack) = extract_packet_and_write_ack_from_tx(event).ok()?;

            let ack = WriteAcknowledgement {
                packet,
                ack: write_ack,
            };

            Some(ack)
        } else {
            None
        }
    }

    fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<Arc<AbciEvent>>>, Error> {
        let events = self.tx_context.send_messages(messages).await?;

        Ok(events)
    }

    async fn query_chain_status(&self) -> Result<ChainStatus, Self::Error> {
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let status = chain_handle
                    .query_application_status()
                    .map_err(BaseError::relayer)?;

                Ok(status)
            })
            .await
            .map_err(BaseError::join)?
    }

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>> {
        &self.subscription
    }
}

#[async_trait]
impl<Chain, Counterparty> OfaIbcChain<CosmosChain<Counterparty>> for CosmosChain<Chain>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
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

    fn log_incoming_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn log_outgoing_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn counterparty_message_height(message: &CosmosIbcMessage) -> Option<Height> {
        message.source_height
    }

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::SendPacket = event_type {
            let (packet, _) = extract_packet_and_write_ack_from_tx(event).ok()?;

            let send_packet_event = SendPacket { packet };

            Some(send_packet_event)
        } else {
            None
        }
    }

    fn extract_packet_from_send_packet_event(
        event: &Self::SendPacketEvent,
    ) -> Self::OutgoingPacket {
        event.packet.clone()
    }

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Self::IncomingPacket {
        &ack.packet
    }

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<ChainId, Error> {
        let chain_handle = self.handle.clone();

        let port_id = port_id.clone();
        let channel_id = channel_id.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let channel_id =
                    counterparty_chain_from_channel(&chain_handle, &channel_id, &port_id)
                        .map_err(BaseError::supervisor)?;

                Ok(channel_id)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<ConsensusState, Error> {
        let chain_handle = self.handle.clone();

        let client_id = client_id.clone();
        let height = *height;

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (any_consensus_state, _) = chain_handle
                    .query_consensus_state(
                        QueryConsensusStateRequest {
                            client_id: client_id.clone(),
                            consensus_height: height,
                            query_height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                match any_consensus_state {
                    AnyConsensusState::Tendermint(consensus_state) => Ok(consensus_state),
                    _ => Err(BaseError::mismatch_consensus_state().into()),
                }
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Error> {
        let chain_handle = self.handle.clone();

        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let sequence = *sequence;

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let unreceived_packet = chain_handle
                    .query_unreceived_packets(QueryUnreceivedPacketsRequest {
                        port_id: port_id.clone(),
                        channel_id: channel_id.clone(),
                        packet_commitment_sequences: vec![sequence],
                    })
                    .map_err(BaseError::relayer)?;

                let is_packet_received = unreceived_packet.is_empty();

                Ok(is_packet_received)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn query_write_acknowledgement_event(
        &self,
        packet: &Packet,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        let status = self.query_chain_status().await?;

        let query_height = Qualified::Equal(status.height);

        let path_ident = PathIdentifiers {
            port_id: packet.destination_port.clone(),
            channel_id: packet.destination_channel.clone(),
            counterparty_port_id: packet.source_port.clone(),
            counterparty_channel_id: packet.source_channel.clone(),
        };

        let chain_handle = self.handle.clone();

        let packet = packet.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let ibc_events = query_write_ack_events(
                    &chain_handle,
                    &path_ident,
                    &[packet.sequence],
                    query_height,
                )
                .map_err(BaseError::relayer)?;

                let write_ack = ibc_events.into_iter().find_map(|event_with_height| {
                    let event = event_with_height.event;

                    if let IbcEvent::WriteAcknowledgement(write_ack) = event {
                        Some(write_ack)
                    } else {
                        None
                    }
                });

                Ok(write_ack)
            })
            .await
            .map_err(BaseError::join)?
    }

    /// Construct a receive packet to be sent to a destination Cosmos
    /// chain from a source Cosmos chain.
    async fn build_receive_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let height = *height;
        let packet = packet.clone();

        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let proofs = chain_handle
                    .build_packet_proofs(
                        PacketMsgType::Recv,
                        &packet.source_port,
                        &packet.source_channel,
                        packet.sequence,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let packet = packet.clone();

                let message = CosmosIbcMessage::new(Some(height), move |signer| {
                    Ok(MsgRecvPacket::new(packet.clone(), proofs.clone(), signer.clone()).to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    /// Construct an acknowledgement packet to be sent from a Cosmos
    /// chain that successfully received a packet from another Cosmos
    /// chain.
    async fn build_ack_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let height = *height;
        let packet = packet.clone();
        let ack = ack.clone();

        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let proofs = chain_handle
                    .build_packet_proofs(
                        PacketMsgType::Ack,
                        &packet.destination_port,
                        &packet.destination_channel,
                        packet.sequence,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let packet = packet.clone();
                let ack = ack.ack.clone();

                let message = CosmosIbcMessage::new(Some(height), move |signer| {
                    Ok(MsgAcknowledgement::new(
                        packet.clone(),
                        ack.clone().into(),
                        proofs.clone(),
                        signer.clone(),
                    )
                    .to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    /// Construct a timeout packet message to be sent between Cosmos chains
    /// over an unordered channel in the event that a packet that originated
    /// from a source chain was not received.
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let height = *height;
        let packet = packet.clone();

        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let proofs = chain_handle
                    .build_packet_proofs(
                        PacketMsgType::TimeoutUnordered,
                        &packet.destination_port,
                        &packet.destination_channel,
                        packet.sequence,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let packet = packet.clone();

                let message = CosmosIbcMessage::new(Some(height), move |signer| {
                    Ok(MsgTimeout::new(
                        packet.clone(),
                        packet.sequence,
                        proofs.clone(),
                        signer.clone(),
                    )
                    .to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }
}
