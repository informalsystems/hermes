use alloc::sync::Arc;
use async_trait::async_trait;
use core::iter;
use eyre::eyre;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::counterparty::counterparty_chain_from_channel;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, Qualified, QueryChannelRequest, QueryClientStateRequest,
    QueryConnectionRequest, QueryConsensusStateHeightsRequest, QueryConsensusStateRequest,
    QueryHeight, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::connection::ConnectionMsgType;
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer::event::{
    channel_open_init_try_from_abci_event, channel_open_try_try_from_abci_event,
    connection_open_ack_try_from_abci_event, connection_open_try_try_from_abci_event,
    extract_packet_and_write_ack_from_tx,
};
use ibc_relayer::light_client::AnyHeader;
use ibc_relayer::link::packet_events::query_write_ack_events;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_all_in_one::one_for_all::traits::chain::{OfaChain, OfaChainTypes, OfaIbcChain};
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_components::chain::traits::message_sender::CanSendMessages;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_runtime::tokio::logger::value::LogValue;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::core::ics02_client::events::CLIENT_ID_ATTRIBUTE_KEY;
use ibc_relayer_types::core::ics02_client::msgs::create_client::MsgCreateClient;
use ibc_relayer_types::core::ics02_client::msgs::update_client::MsgUpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc_relayer_types::core::ics03_connection::version::Version as ConnectionVersion;
use ibc_relayer_types::core::ics04_channel::channel::{
    ChannelEnd, Counterparty as ChannelCounterparty, State,
};
use ibc_relayer_types::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc_relayer_types::core::ics04_channel::msgs::acknowledgement::MsgAcknowledgement;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
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
use crate::types::channel::{
    CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenInitEvent,
    CosmosChannelOpenTryEvent, CosmosChannelOpenTryPayload, CosmosInitChannelOptions,
};
use crate::types::client::{
    CosmosCreateClientEvent, CosmosCreateClientPayload, CosmosUpdateClientPayload,
};
use crate::types::connection::{
    CosmosConnectionOpenAckPayload, CosmosConnectionOpenConfirmPayload,
    CosmosConnectionOpenInitEvent, CosmosConnectionOpenInitPayload, CosmosConnectionOpenTryEvent,
    CosmosConnectionOpenTryPayload, CosmosInitConnectionOptions,
};
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;
use crate::types::telemetry::CosmosTelemetry;

#[async_trait]
impl<Chain> OfaChainTypes for CosmosChain<Chain>
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
    type IncomingPacket = Packet;

    type OutgoingPacket = Packet;

    type ClientState = ClientState;

    type CreateClientPayloadOptions = ClientSettings;

    type CreateClientPayload = CosmosCreateClientPayload;

    type CreateClientEvent = CosmosCreateClientEvent;

    type UpdateClientPayload = CosmosUpdateClientPayload;

    type ConnectionVersion = ConnectionVersion;

    type ConnectionDetails = ConnectionEnd;

    type ConnectionOpenInitEvent = CosmosConnectionOpenInitEvent;

    type ConnectionOpenTryEvent = CosmosConnectionOpenTryEvent;

    type InitConnectionOptions = CosmosInitConnectionOptions;

    type ConnectionOpenInitPayload = CosmosConnectionOpenInitPayload;

    type ConnectionOpenTryPayload = CosmosConnectionOpenTryPayload;

    type ConnectionOpenAckPayload = CosmosConnectionOpenAckPayload;

    type ConnectionOpenConfirmPayload = CosmosConnectionOpenConfirmPayload;

    type InitChannelOptions = CosmosInitChannelOptions;

    type ChannelOpenTryPayload = CosmosChannelOpenTryPayload;

    type ChannelOpenAckPayload = CosmosChannelOpenAckPayload;

    type ChannelOpenConfirmPayload = CosmosChannelOpenConfirmPayload;

    type ChannelOpenInitEvent = CosmosChannelOpenInitEvent;

    type ChannelOpenTryEvent = CosmosChannelOpenTryEvent;
}

#[async_trait]
impl<Chain> OfaChain for CosmosChain<Chain>
where
    Chain: ChainHandle,
{
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
impl<Chain, Counterparty> OfaIbcChain<Counterparty> for CosmosChain<Chain>
where
    Chain: ChainHandle,
    Counterparty: OfaChainTypes<
        // A Cosmos chain can act as an IBC chain to a counterparty,
        // as long as the counterparty uses the same base Cosmos types.
        ChainId = ChainId,
        Height = Height,
        Message = CosmosIbcMessage,
        Timestamp = Timestamp,
        IncomingPacket = Packet,
        OutgoingPacket = Packet,
        ClientId = ClientId,
        ConnectionId = ConnectionId,
        ChannelId = ChannelId,
        PortId = PortId,
        Sequence = Sequence,
        // TODO: Support other counterparty client types and payload types
        // provided that we can build Cosmos messages for it.
        ClientState = ClientState,
        ConsensusState = ConsensusState,
        CreateClientPayload = CosmosCreateClientPayload,
        UpdateClientPayload = CosmosUpdateClientPayload,
        ConnectionOpenInitPayload = CosmosConnectionOpenInitPayload,
        ConnectionOpenTryPayload = CosmosConnectionOpenTryPayload,
        ConnectionOpenAckPayload = CosmosConnectionOpenAckPayload,
        ConnectionOpenConfirmPayload = CosmosConnectionOpenConfirmPayload,
        ChannelOpenTryPayload = CosmosChannelOpenTryPayload,
        ChannelOpenAckPayload = CosmosChannelOpenAckPayload,
        ChannelOpenConfirmPayload = CosmosChannelOpenConfirmPayload,
    >,
{
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

    fn client_state_latest_height(client_state: &Self::ClientState) -> &Self::Height {
        &client_state.latest_height
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

    fn try_extract_create_client_event(event: Arc<AbciEvent>) -> Option<Self::CreateClientEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::CreateClient = event_type {
            for tag in &event.attributes {
                let key = tag.key.as_str();
                let value = tag.value.as_str();
                if key == CLIENT_ID_ATTRIBUTE_KEY {
                    let client_id = value.parse().ok()?;

                    return Some(CosmosCreateClientEvent { client_id });
                }
            }

            None
        } else {
            None
        }
    }

    fn create_client_event_client_id(event: &CosmosCreateClientEvent) -> &Self::ClientId {
        &event.client_id
    }

    fn try_extract_connection_open_init_event(
        event: Arc<AbciEvent>,
    ) -> Option<CosmosConnectionOpenInitEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenInitConnection = event_type {
            let open_ack_event = connection_open_ack_try_from_abci_event(&event).ok()?;

            let connection_id = open_ack_event.connection_id()?.clone();

            Some(CosmosConnectionOpenInitEvent { connection_id })
        } else {
            None
        }
    }

    fn connection_open_init_event_connection_id(
        event: &CosmosConnectionOpenInitEvent,
    ) -> &ConnectionId {
        &event.connection_id
    }

    fn try_extract_connection_open_try_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenTryEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenTryConnection = event_type {
            let open_try_event = connection_open_try_try_from_abci_event(&event).ok()?;

            let connection_id = open_try_event.connection_id()?.clone();

            Some(CosmosConnectionOpenTryEvent { connection_id })
        } else {
            None
        }
    }

    fn connection_open_try_event_connection_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> &Self::ConnectionId {
        &event.connection_id
    }

    fn try_extract_channel_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ChannelOpenInitEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenInitChannel = event_type {
            let open_init_event = channel_open_init_try_from_abci_event(&event).ok()?;

            let channel_id = open_init_event.channel_id()?.clone();

            Some(CosmosChannelOpenInitEvent { channel_id })
        } else {
            None
        }
    }

    fn channel_open_try_event_channel_id(event: &Self::ChannelOpenTryEvent) -> &Self::ChannelId {
        &event.channel_id
    }

    fn try_extract_channel_open_try_event(event: Self::Event) -> Option<Self::ChannelOpenTryEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenTryChannel = event_type {
            let open_try_event = channel_open_try_try_from_abci_event(&event).ok()?;

            let channel_id = open_try_event.channel_id()?.clone();

            Some(CosmosChannelOpenTryEvent { channel_id })
        } else {
            None
        }
    }

    fn channel_open_init_event_channel_id(event: &Self::ChannelOpenInitEvent) -> &Self::ChannelId {
        &event.channel_id
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

    async fn query_client_state(&self, client_id: &ClientId) -> Result<ClientState, Error> {
        let chain_handle = self.handle.clone();

        let client_id = client_id.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (client_state, _) = chain_handle
                    .query_client_state(
                        QueryClientStateRequest {
                            client_id,
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                match client_state {
                    AnyClientState::Tendermint(client_state) => Ok(client_state),
                    _ => Err(BaseError::generic(eyre!("expected tendermint client state")).into()),
                }
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

    async fn query_is_packet_received(
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

    async fn build_create_client_payload(
        &self,
        client_settings: &ClientSettings,
    ) -> Result<CosmosCreateClientPayload, Self::Error> {
        let client_settings = client_settings.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let height = chain_handle
                    .query_latest_height()
                    .map_err(BaseError::relayer)?;

                let any_client_state = chain_handle
                    .build_client_state(height, client_settings)
                    .map_err(BaseError::relayer)?;

                let client_state = match &any_client_state {
                    AnyClientState::Tendermint(client_state) => client_state.clone(),
                    _ => {
                        return Err(
                            BaseError::generic(eyre!("expect Tendermint client state")).into()
                        );
                    }
                };

                let any_consensus_state = chain_handle
                    .build_consensus_state(
                        any_client_state.latest_height(),
                        height,
                        any_client_state,
                    )
                    .map_err(BaseError::relayer)?;

                let consensus_state = match any_consensus_state {
                    AnyConsensusState::Tendermint(consensus_state) => consensus_state,
                    _ => {
                        return Err(
                            BaseError::generic(eyre!("expect Tendermint consensus state")).into(),
                        );
                    }
                };

                Ok(CosmosCreateClientPayload {
                    client_state,
                    consensus_state,
                })
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_create_client_message(
        &self,
        payload: CosmosCreateClientPayload,
    ) -> Result<CosmosIbcMessage, Self::Error> {
        let message = CosmosIbcMessage::new(None, move |signer| {
            let message = MsgCreateClient {
                client_state: payload.client_state.clone().into(),
                consensus_state: payload.consensus_state.clone().into(),
                signer: signer.clone(),
            };

            Ok(message.to_any())
        });

        Ok(message)
    }

    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<CosmosConnectionOpenInitPayload, Error> {
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let commitment_prefix = chain_handle
                    .query_commitment_prefix()
                    .map_err(BaseError::relayer)?;

                Ok(CosmosConnectionOpenInitPayload { commitment_prefix })
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_update_client_payload(
        &self,
        trusted_height: &Height,
        target_height: &Height,
        client_state: ClientState,
    ) -> Result<CosmosUpdateClientPayload, Self::Error> {
        let trusted_height = *trusted_height;
        let target_height = *target_height;
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (header, support) = chain_handle
                    .build_header(
                        trusted_height,
                        target_height,
                        AnyClientState::Tendermint(client_state),
                    )
                    .map_err(BaseError::relayer)?;

                let headers = iter::once(header)
                    .chain(support.into_iter())
                    .map(|header| match header {
                        AnyHeader::Tendermint(header) => Ok(header),
                        _ => Err(BaseError::generic(eyre!("expect tendermint header")).into()),
                    })
                    .collect::<Result<Vec<TendermintHeader>, Error>>()?;

                Ok(CosmosUpdateClientPayload { headers })
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        payload: CosmosUpdateClientPayload,
    ) -> Result<Vec<Self::Message>, Self::Error> {
        let messages = payload
            .headers
            .into_iter()
            .map(|header| {
                let client_id = client_id.clone();
                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgUpdateClient {
                        client_id: client_id.clone(),
                        header: header.clone().into(),
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                message
            })
            .collect();

        Ok(messages)
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, Error> {
        let client_id = client_id.clone();
        let target_height = *target_height;

        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let heights = {
                    let mut heights = chain_handle
                        .query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                            client_id,
                            pagination: Some(PageRequest::all()),
                        })
                        .map_err(BaseError::relayer)?;

                    heights.sort_by_key(|&h| core::cmp::Reverse(h));

                    heights
                };

                let height = heights
                    .into_iter()
                    .find(|height| height < &target_height)
                    .ok_or_else(|| {
                        BaseError::generic(eyre!(
                            "no consensus state found that is smaller than target height {}",
                            target_height
                        ))
                    })?;

                Ok(height)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Error> {
        let height = *height;
        let client_id = client_id.clone();
        let connection_id = connection_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let commitment_prefix = chain_handle
                    .query_commitment_prefix()
                    .map_err(BaseError::relayer)?;

                let (connection, _) = chain_handle
                    .query_connection(
                        QueryConnectionRequest {
                            connection_id: connection_id.clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                let versions = connection.versions().to_vec();
                let delay_period = connection.delay_period();

                let (client_state, proofs) = chain_handle
                    .build_connection_proofs_and_client_state(
                        ConnectionMsgType::OpenTry,
                        &connection_id,
                        &client_id,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let payload = CosmosConnectionOpenTryPayload {
                    commitment_prefix,
                    proofs,
                    client_state,
                    versions,
                    delay_period,
                };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Error> {
        let height = *height;
        let client_id = client_id.clone();
        let connection_id = connection_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (connection, _) = chain_handle
                    .query_connection(
                        QueryConnectionRequest {
                            connection_id: connection_id.clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                let version = connection
                    .versions()
                    .iter()
                    .next()
                    .cloned()
                    .unwrap_or_default();

                let (client_state, proofs) = chain_handle
                    .build_connection_proofs_and_client_state(
                        ConnectionMsgType::OpenAck,
                        &connection_id,
                        &client_id,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let payload = CosmosConnectionOpenAckPayload {
                    proofs,
                    client_state,
                    version,
                };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Error> {
        let height = *height;
        let client_id = client_id.clone();
        let connection_id = connection_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (_, proofs) = chain_handle
                    .build_connection_proofs_and_client_state(
                        ConnectionMsgType::OpenConfirm,
                        &connection_id,
                        &client_id,
                        height,
                    )
                    .map_err(BaseError::relayer)?;

                let payload = CosmosConnectionOpenConfirmPayload { proofs };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &CosmosInitConnectionOptions,
        counterparty_payload: CosmosConnectionOpenInitPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let counterparty = ConnectionCounterparty::new(
            counterparty_client_id.clone(),
            None,
            counterparty_payload.commitment_prefix,
        );

        let client_id = client_id.clone();
        let delay_period = init_connection_options.delay_period;
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let versions = chain_handle
                    .query_compatible_versions()
                    .map_err(BaseError::relayer)?;

                let version = versions.into_iter().next().unwrap_or_default();

                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgConnectionOpenInit {
                        client_id: client_id.clone(),
                        counterparty: counterparty.clone(),
                        version: Some(version.clone()),
                        delay_period,
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenTryPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let client_id = client_id.clone();
        let counterparty = ConnectionCounterparty::new(
            counterparty_client_id.clone(),
            Some(counterparty_connection_id.clone()),
            counterparty_payload.commitment_prefix.clone(),
        );

        let message = CosmosIbcMessage::new(None, move |signer| {
            let client_state = counterparty_payload.client_state.clone().map(Into::into);
            let counterparty_versions: Vec<ConnectionVersion> =
                counterparty_payload.versions.clone();
            let proofs = counterparty_payload.proofs.clone();
            let delay_period = counterparty_payload.delay_period;
            let counterparty = counterparty.clone();

            let message = MsgConnectionOpenTry {
                client_id: client_id.clone(),
                client_state,
                counterparty,
                counterparty_versions,
                delay_period,
                proofs,
                signer: signer.clone(),
                previous_connection_id: None, // deprecated
            };

            Ok(message.to_any())
        });

        Ok(message)
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenAckPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let connection_id = connection_id.clone();
        let counterparty_connection_id = counterparty_connection_id.clone();

        let message = CosmosIbcMessage::new(None, move |signer| {
            let version = counterparty_payload.version.clone();
            let client_state = counterparty_payload.client_state.clone().map(Into::into);
            let proofs = counterparty_payload.proofs.clone();

            let message = MsgConnectionOpenAck {
                connection_id: connection_id.clone(),
                counterparty_connection_id: counterparty_connection_id.clone(),
                version,
                client_state,
                proofs,
                signer: signer.clone(),
            };

            Ok(message.to_any())
        });

        Ok(message)
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenConfirmPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let connection_id = connection_id.clone();

        let message = CosmosIbcMessage::new(None, move |signer| {
            let proofs: ibc_relayer_types::proofs::Proofs = counterparty_payload.proofs.clone();

            let message = MsgConnectionOpenConfirm {
                connection_id: connection_id.clone(),
                proofs,
                signer: signer.clone(),
            };

            Ok(message.to_any())
        });

        Ok(message)
    }

    async fn build_channel_open_try_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Self::Error> {
        let height = *height;
        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (channel_end, _) = chain_handle
                    .query_channel(
                        QueryChannelRequest {
                            port_id: port_id.clone(),
                            channel_id: channel_id.clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                let proofs = chain_handle
                    .build_channel_proofs(&port_id, &channel_id, height)
                    .map_err(BaseError::relayer)?;

                let payload = CosmosChannelOpenTryPayload {
                    previous_channel_id: channel_end.counterparty().channel_id.clone(),
                    proofs,
                    ordering: channel_end.ordering,
                    connection_hops: channel_end.connection_hops,
                    version: channel_end.version,
                };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_ack_payload(
        &self,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenAckPayload, Self::Error> {
        let height = *height;
        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let (channel_end, _) = chain_handle
                    .query_channel(
                        QueryChannelRequest {
                            port_id: port_id.clone(),
                            channel_id: channel_id.clone(),
                            height: QueryHeight::Latest,
                        },
                        IncludeProof::No,
                    )
                    .map_err(BaseError::relayer)?;

                let proofs = chain_handle
                    .build_channel_proofs(&port_id, &channel_id, height)
                    .map_err(BaseError::relayer)?;

                let payload = CosmosChannelOpenAckPayload {
                    proofs,
                    version: channel_end.version,
                };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_confirm_payload(
        &self,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenConfirmPayload, Self::Error> {
        let height = *height;
        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let chain_handle = self.handle.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let proofs = chain_handle
                    .build_channel_proofs(&port_id, &channel_id, height)
                    .map_err(BaseError::relayer)?;

                let payload = CosmosChannelOpenConfirmPayload { proofs };

                Ok(payload)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_init_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        init_channel_options: &CosmosInitChannelOptions,
    ) -> Result<CosmosIbcMessage, Error> {
        let port_id = port_id.clone();
        let ordering = init_channel_options.ordering;
        let connection_hops = init_channel_options.connection_hops.clone();
        let channel_version = init_channel_options.channel_version.clone();

        let counterparty = ChannelCounterparty::new(counterparty_port_id.clone(), None);

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let channel = ChannelEnd::new(
                    State::Init,
                    ordering,
                    counterparty,
                    connection_hops,
                    channel_version,
                );

                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgChannelOpenInit {
                        port_id: port_id.clone(),
                        channel: channel.clone(),
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_try_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenTryPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let port_id = port_id.clone();
        let counterparty = ChannelCounterparty::new(
            counterparty_port_id.clone(),
            Some(counterparty_channel_id.clone()),
        );
        let ordering = counterparty_payload.ordering;
        let connection_hops = counterparty_payload.connection_hops.clone();
        let version = counterparty_payload.version.clone();
        let previous_channel_id = counterparty_payload.previous_channel_id.clone();
        let proofs = counterparty_payload.proofs.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let channel = ChannelEnd::new(
                    State::TryOpen,
                    ordering,
                    counterparty,
                    connection_hops,
                    version.clone(),
                );
                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgChannelOpenTry {
                        port_id: port_id.clone(),
                        previous_channel_id: previous_channel_id.clone(),
                        channel: channel.clone(),
                        counterparty_version: version.clone(),
                        proofs: proofs.clone(),
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenAckPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let counterparty_channel_id = counterparty_channel_id.clone();
        let counterparty_version = counterparty_payload.version.clone();
        let proofs = counterparty_payload.proofs.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgChannelOpenAck {
                        port_id: port_id.clone(),
                        channel_id: channel_id.clone(),
                        counterparty_channel_id: counterparty_channel_id.clone(),
                        counterparty_version: counterparty_version.clone(),
                        proofs: proofs.clone(),
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenConfirmPayload,
    ) -> Result<CosmosIbcMessage, Error> {
        let port_id = port_id.clone();
        let channel_id = channel_id.clone();
        let proofs = counterparty_payload.proofs.clone();

        self.runtime
            .runtime
            .runtime
            .spawn_blocking(move || {
                let message = CosmosIbcMessage::new(None, move |signer| {
                    let message = MsgChannelOpenConfirm {
                        port_id: port_id.clone(),
                        channel_id: channel_id.clone(),
                        proofs: proofs.clone(),
                        signer: signer.clone(),
                    };

                    Ok(message.to_any())
                });

                Ok(message)
            })
            .await
            .map_err(BaseError::join)?
    }
}
