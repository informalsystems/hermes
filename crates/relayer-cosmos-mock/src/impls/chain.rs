use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;

use basecoin_app::modules::ibc::AnyConsensusState;
use ibc::clients::ics07_tendermint::client_state::{AllowUpdate, ClientState as TmClientState};
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc::core::events::IbcEvent;
use ibc::core::ics02_client::events::CreateClient;
use ibc::core::ics02_client::msgs::create_client::MsgCreateClient;
use ibc::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc::core::ics04_channel::msgs::{MsgAcknowledgement, MsgRecvPacket, MsgTimeout};
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics04_channel::timeout::TimeoutHeight;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::core::ics24_host::path::{AckPath, ClientConsensusStatePath, ReceiptPath};
use ibc::core::timestamp::Timestamp;
use ibc::core::{Msg, ValidationContext};
use ibc::Any;
use ibc::Height;

use ibc_relayer_components::chain::traits::client::create::CanBuildCreateClientMessage;
use ibc_relayer_components::chain::traits::client::create::CanBuildCreateClientPayload;
use ibc_relayer_components::chain::traits::client::create::HasCreateClientEvent;
use ibc_relayer_components::chain::traits::client::create::HasCreateClientOptions;
use ibc_relayer_components::chain::traits::client::create::HasCreateClientPayload;
use ibc_relayer_components::chain::traits::logs::event::CanLogChainEvent;
use ibc_relayer_components::chain::traits::logs::packet::CanLogChainPacket;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::CanBuildAckPacketMessage;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::CanBuildAckPacketPayload;
use ibc_relayer_components::chain::traits::message_builders::receive_packet::CanBuildReceivePacketMessage;
use ibc_relayer_components::chain::traits::message_builders::receive_packet::CanBuildReceivePacketPayload;
use ibc_relayer_components::chain::traits::message_builders::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use ibc_relayer_components::chain::traits::message_builders::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketPayload;
use ibc_relayer_components::chain::traits::message_sender::CanSendMessages;
use ibc_relayer_components::chain::traits::queries::consensus_state::CanQueryConsensusState;
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;
use ibc_relayer_components::chain::traits::queries::status::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::queries::write_ack::CanQueryWriteAcknowledgement;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainIdType;
use ibc_relayer_components::chain::traits::types::client_state::HasClientStateType;
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::height::CanIncrementHeight;
use ibc_relayer_components::chain::traits::types::height::HasHeightType;
use ibc_relayer_components::chain::traits::types::ibc::HasCounterpartyMessageHeight;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::message::CanEstimateMessageSize;
use ibc_relayer_components::chain::traits::types::message::HasMessageType;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketFields;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketTypes;
use ibc_relayer_components::chain::traits::types::packets::ack::HasAckPacketPayload;
use ibc_relayer_components::chain::traits::types::packets::receive::HasReceivePacketPayload;
use ibc_relayer_components::chain::traits::types::packets::timeout::HasTimeoutUnorderedPacketPayload;
use ibc_relayer_components::chain::traits::types::status::HasChainStatusType;
use ibc_relayer_components::chain::traits::types::timestamp::HasTimestampType;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::logger::traits::has_logger::HasLogger;
use ibc_relayer_components::logger::traits::has_logger::HasLoggerType;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use ibc_relayer_runtime::types::error::Error as TokioError;
use ibc_relayer_runtime::types::log::logger::TracingLogger;
use ibc_relayer_runtime::types::log::value::LogValue;

use crate::contexts::chain::MockCosmosContext;
use crate::contexts::runtime::MockRuntimeContext;
use crate::traits::endpoint::{BasecoinEndpoint, QueryService};
use crate::types::error::Error;
use crate::types::status::ChainStatus;
use crate::util::dummy::dummy_signer;

impl<Chain: BasecoinEndpoint> HasErrorType for MockCosmosContext<Chain> {
    type Error = Error;
}

impl<Chain: BasecoinEndpoint> HasRuntime for MockCosmosContext<Chain> {
    type Runtime = MockRuntimeContext;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }

    fn runtime_error(e: TokioError) -> Error {
        Error::source(e)
    }
}

impl<Chain: BasecoinEndpoint> HasLoggerType for MockCosmosContext<Chain> {
    type Logger = TracingLogger;
}

impl<Chain: BasecoinEndpoint> HasLogger for MockCosmosContext<Chain> {
    fn logger(&self) -> &TracingLogger {
        &TracingLogger
    }
}

impl<Chain: BasecoinEndpoint> HasChainIdType for MockCosmosContext<Chain> {
    type ChainId = ChainId;
}

impl<Chain: BasecoinEndpoint> HasChainId for MockCosmosContext<Chain> {
    fn chain_id(&self) -> &Self::ChainId {
        self.get_chain_id()
    }
}

impl<Chain: BasecoinEndpoint> HasHeightType for MockCosmosContext<Chain> {
    type Height = Height;
}

impl<Chain: BasecoinEndpoint> HasEventType for MockCosmosContext<Chain> {
    type Event = IbcEvent;
}

impl<Chain: BasecoinEndpoint> CanLogChainEvent for MockCosmosContext<Chain> {
    fn log_event<'a>(event: &Self::Event) -> LogValue<'_> {
        LogValue::Debug(event)
    }
}

impl<Chain: BasecoinEndpoint> HasTimestampType for MockCosmosContext<Chain> {
    type Timestamp = Timestamp;
}

impl<Chain: BasecoinEndpoint> HasMessageType for MockCosmosContext<Chain> {
    type Message = Any;
}

impl<SrcChain, DstChain> HasIbcChainTypes<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;
}

impl<SrcChain, DstChain> HasIbcPacketTypes<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type IncomingPacket = Packet;

    type OutgoingPacket = Packet;
}

impl<SrcChain, DstChain> CanLogChainPacket<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    fn log_incoming_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn log_outgoing_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }
}

impl<SrcChain, DstChain> HasIbcPacketFields<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    fn incoming_packet_src_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId {
        &packet.chan_id_on_a
    }

    fn incoming_packet_src_port(packet: &Self::IncomingPacket) -> &Self::PortId {
        &packet.port_id_on_a
    }

    fn incoming_packet_dst_channel_id(packet: &Self::IncomingPacket) -> &Self::ChannelId {
        &packet.chan_id_on_b
    }

    fn incoming_packet_dst_port(packet: &Self::IncomingPacket) -> &Self::PortId {
        &packet.port_id_on_b
    }

    fn incoming_packet_sequence(packet: &Self::IncomingPacket) -> &Self::Sequence {
        &packet.seq_on_a
    }

    fn incoming_packet_timeout_height(packet: &Self::IncomingPacket) -> Option<&Self::Height> {
        match &packet.timeout_height_on_b {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(height) => Some(height),
        }
    }

    fn incoming_packet_timeout_timestamp(packet: &Self::IncomingPacket) -> &Self::Timestamp {
        &packet.timeout_timestamp_on_b
    }

    fn outgoing_packet_src_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId {
        &packet.chan_id_on_a
    }

    fn outgoing_packet_src_port(packet: &Self::OutgoingPacket) -> &Self::PortId {
        &packet.port_id_on_a
    }

    fn outgoing_packet_dst_port(packet: &Self::OutgoingPacket) -> &Self::PortId {
        &packet.port_id_on_b
    }

    fn outgoing_packet_dst_channel_id(packet: &Self::OutgoingPacket) -> &Self::ChannelId {
        &packet.chan_id_on_b
    }

    fn outgoing_packet_sequence(packet: &Self::OutgoingPacket) -> &Self::Sequence {
        &packet.seq_on_a
    }

    fn outgoing_packet_timeout_height(packet: &Self::OutgoingPacket) -> Option<&Self::Height> {
        match &packet.timeout_height_on_b {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(height) => Some(height),
        }
    }

    fn outgoing_packet_timeout_timestamp(packet: &Self::OutgoingPacket) -> &Self::Timestamp {
        &packet.timeout_timestamp_on_b
    }
}

impl<SrcChain, DstChain> HasConsensusStateType<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type ConsensusState = TmConsensusState;
}

impl<SrcChain, DstChain> HasClientStateType<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type ClientState = TmClientState;
}

impl<Chain: BasecoinEndpoint> HasChainStatusType for MockCosmosContext<Chain> {
    type ChainStatus = ChainStatus;

    fn chain_status_height(status: &Self::ChainStatus) -> &Self::Height {
        &status.height
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Self::Timestamp {
        &status.timestamp
    }
}

#[async_trait]
impl<Chain: BasecoinEndpoint> CanQueryChainStatus for MockCosmosContext<Chain> {
    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Self::Error> {
        Ok(self.current_status.lock().unwrap().clone())
    }
}

impl<SrcChain, DstChain> HasCreateClientOptions<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type CreateClientPayloadOptions = ();
}

impl<SrcChain, DstChain> HasCreateClientPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type CreateClientPayload = Any;
}

impl<SrcChain, DstChain> HasCreateClientEvent<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type CreateClientEvent = CreateClient;

    fn try_extract_create_client_event(event: Self::Event) -> Option<Self::CreateClientEvent> {
        match event {
            IbcEvent::CreateClient(e) => Some(e.clone()),
            _ => None,
        }
    }

    fn create_client_event_client_id(event: &Self::CreateClientEvent) -> &Self::ClientId {
        event.client_id()
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildCreateClientPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_create_client_payload(
        &self,
        _create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<Self::CreateClientPayload, Self::Error> {
        let tm_client_state = TmClientState::new(
            self.get_chain_id().clone(),
            Default::default(),
            Duration::from_secs(64000),
            Duration::from_secs(128000),
            Duration::from_millis(3000),
            self.get_current_height(),
            Default::default(),
            Default::default(),
            AllowUpdate {
                after_expiry: false,
                after_misbehaviour: false,
            },
        )?;

        let current_height = self.get_current_height();

        let any_consensus_state = self.ibc_context().host_consensus_state(&current_height)?;

        let AnyConsensusState::Tendermint(tm_consensus_state) = any_consensus_state;

        let msg_create_client = MsgCreateClient {
            client_state: tm_client_state.into(),
            consensus_state: tm_consensus_state.into(),
            signer: dummy_signer(),
        };

        Ok(msg_create_client.to_any())
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildCreateClientMessage<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_create_client_message(
        &self,
        counterparty_payload: Any,
    ) -> Result<Any, Self::Error> {
        Ok(counterparty_payload)
    }
}

impl<SrcChain, DstChain> HasSendPacketEvent<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type SendPacketEvent = SendPacket;

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent> {
        match event {
            IbcEvent::SendPacket(e) => Some(e.clone()),
            _ => None,
        }
    }

    fn extract_packet_from_send_packet_event(
        event: &Self::SendPacketEvent,
    ) -> Self::OutgoingPacket {
        Packet {
            seq_on_a: *event.seq_on_a(),
            port_id_on_a: event.port_id_on_a().clone(),
            chan_id_on_a: event.chan_id_on_a().clone(),
            port_id_on_b: event.port_id_on_b().clone(),
            chan_id_on_b: event.chan_id_on_b().clone(),
            data: event.packet_data().to_vec(),
            timeout_height_on_b: *event.timeout_height_on_b(),
            timeout_timestamp_on_b: *event.timeout_timestamp_on_b(),
        }
    }
}

impl<Chain: BasecoinEndpoint> CanIncrementHeight for MockCosmosContext<Chain> {
    fn increment_height(height: &Self::Height) -> Result<Self::Height, Self::Error> {
        Ok(height.increment())
    }
}

impl<Chain: BasecoinEndpoint> CanEstimateMessageSize for MockCosmosContext<Chain> {
    fn estimate_message_size(_message: &Self::Message) -> Result<usize, Self::Error> {
        // Only single messages are sent by the Mock Chain
        Ok(1)
    }
}

#[async_trait]
impl<Chain: BasecoinEndpoint> CanSendMessages for MockCosmosContext<Chain> {
    async fn send_messages(
        &self,
        messages: Vec<Self::Message>,
    ) -> Result<Vec<Vec<Self::Event>>, Error> {
        self.submit_messages(messages)
    }
}

impl<SrcChain, DstChain> HasCounterpartyMessageHeight<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    fn counterparty_message_height_for_update_client(_message: &Any) -> Option<Height> {
        None
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanQueryConsensusState<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<TmConsensusState, Error> {
        let path = ClientConsensusStatePath::new(client_id, height);

        let any_cons_state: AnyConsensusState = self.ibc_context().consensus_state(&path)?;

        let tm_consensus_state =
            TmConsensusState::try_from(any_cons_state).map_err(Error::source)?;

        Ok(tm_consensus_state)
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanQueryReceivedPacket<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Self::Sequence,
    ) -> Result<bool, Self::Error> {
        let path = ReceiptPath::new(port_id, channel_id, *sequence);

        let receipt = self.ibc_context().get_packet_receipt(&path);

        Ok(receipt.is_ok())
    }
}

impl<SrcChain, DstChain> HasReceivePacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type ReceivePacketPayload = Any;
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildReceivePacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_receive_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::ReceivePacketPayload, Error> {
        let receipt_path =
            ReceiptPath::new(&packet.port_id_on_a, &packet.chan_id_on_a, packet.seq_on_a);

        let (_, proof_commitment_on_a) = self.query(receipt_path, height).await?;

        let recv_packet_payload = MsgRecvPacket {
            packet: packet.clone(),
            proof_commitment_on_a,
            proof_height_on_a: *height,
            signer: dummy_signer(),
        };

        Ok(recv_packet_payload.to_any())
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildReceivePacketMessage<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_receive_packet_message(
        &self,
        _packet: &Packet,
        payload: Any,
    ) -> Result<Any, Error> {
        Ok(payload)
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanQueryWriteAcknowledgement<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn query_write_acknowledgement_event(
        &self,
        packet: &Packet,
    ) -> Result<Option<WriteAcknowledgement>, Error> {
        let chan_counter = self.ibc_context().channel_counter()?;

        let chan_id = ChannelId::new(chan_counter);

        let port_id = PortId::transfer();

        let ack_path = AckPath::new(&port_id, &chan_id, packet.seq_on_a);

        self.ibc_context().get_packet_acknowledgement(&ack_path)?;

        let events = self.ibc_context().events();

        for e in events {
            if let IbcEvent::WriteAcknowledgement(e) = e {
                if e.port_id_on_a() == &port_id
                    && e.chan_id_on_a() == &chan_id
                    && e.seq_on_a() == &packet.seq_on_a
                {
                    return Ok(Some(e));
                }
            }
        }

        Ok(None)
    }
}

impl<SrcChain, DstChain> HasWriteAcknowledgementEvent<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type WriteAcknowledgementEvent = WriteAcknowledgement;

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        match event {
            IbcEvent::WriteAcknowledgement(e) => Some(e.clone()),
            _ => None,
        }
    }
}

impl<SrcChain, DstChain> HasAckPacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type AckPacketPayload = Any;
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildAckPacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_ack_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Self::AckPacketPayload, Error> {
        let ack_path = AckPath::new(&packet.port_id_on_a, &packet.chan_id_on_a, packet.seq_on_a);

        let (_, proof_acked_on_b) = self.query(ack_path, height).await?;

        let ack_packet_payload = MsgAcknowledgement {
            packet: packet.clone(),
            acknowledgement: ack.acknowledgement().clone(),
            proof_acked_on_b,
            proof_height_on_b: self.get_current_height(),
            signer: dummy_signer(),
        };

        Ok(ack_packet_payload.to_any())
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildAckPacketMessage<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_ack_packet_message(&self, _packet: &Packet, payload: Any) -> Result<Any, Error> {
        Ok(payload)
    }
}

impl<SrcChain, DstChain> HasTimeoutUnorderedPacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    type TimeoutUnorderedPacketPayload = Any;
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildTimeoutUnorderedPacketPayload<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_timeout_unordered_packet_payload(
        &self,
        _client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Error> {
        let receipt_path =
            ReceiptPath::new(&packet.port_id_on_a, &packet.chan_id_on_a, packet.seq_on_a);

        let (_, proof_acked_on_b) = self.query(receipt_path, height).await?;

        let ack_packet_payload = MsgTimeout {
            packet: packet.clone(),
            next_seq_recv_on_b: packet.seq_on_a.increment(),
            proof_unreceived_on_b: proof_acked_on_b,
            proof_height_on_b: self.get_current_height(),
            signer: dummy_signer(),
        };

        Ok(ack_packet_payload.to_any())
    }
}

#[async_trait]
impl<SrcChain, DstChain> CanBuildTimeoutUnorderedPacketMessage<MockCosmosContext<DstChain>>
    for MockCosmosContext<SrcChain>
where
    SrcChain: BasecoinEndpoint,
    DstChain: BasecoinEndpoint,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        _packet: &Packet,
        payload: Any,
    ) -> Result<Any, Error> {
        Ok(payload)
    }
}

impl<Endpoint> QueryService for MockCosmosContext<Endpoint>
where
    Endpoint: BasecoinEndpoint,
{
    type Endpoint = Endpoint;

    fn service(&self) -> &Arc<Self::Endpoint> {
        &self.querier
    }
}
