use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::event::{
    channel_open_init_try_from_abci_event, channel_open_try_try_from_abci_event,
    connection_open_ack_try_from_abci_event, connection_open_try_try_from_abci_event,
    extract_packet_and_write_ack_from_tx,
};
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
use ibc_relayer_types::core::ics02_client::events::CLIENT_ID_ATTRIBUTE_KEY;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics03_connection::version::Version as ConnectionVersion;
use ibc_relayer_types::core::ics04_channel::events::{SendPacket, WriteAcknowledgement};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::events::IbcEventType;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;
use prost::Message as _;
use tendermint::abci::Event as AbciEvent;

use crate::contexts::chain::CosmosChain;
use crate::methods::chain::query_chain_status;
use crate::methods::channel::{
    build_channel_open_ack_message, build_channel_open_ack_payload,
    build_channel_open_confirm_message, build_channel_open_confirm_payload,
    build_channel_open_init_message, build_channel_open_try_message,
    build_channel_open_try_payload, query_chain_id_from_channel_id,
};
use crate::methods::client_state::query_client_state;
use crate::methods::connection::{
    build_connection_open_ack_message, build_connection_open_ack_payload,
    build_connection_open_confirm_message, build_connection_open_confirm_payload,
    build_connection_open_init_message, build_connection_open_init_payload,
    build_connection_open_try_message, build_connection_open_try_payload,
};
use crate::methods::consensus_state::{find_consensus_state_height_before, query_consensus_state};
use crate::methods::create_client::{build_create_client_message, build_create_client_payload};
use crate::methods::packet::{
    build_ack_packet_message, build_ack_packet_payload, build_receive_packet_message,
    build_receive_packet_payload, build_timeout_unordered_packet_message,
    build_timeout_unordered_packet_payload, query_is_packet_received,
    query_write_acknowledgement_event,
};
use crate::methods::unreceived_packet::{
    query_packet_commitments, query_unreceived_packet_sequences, query_unreceived_packets,
};
use crate::methods::update_client::{build_update_client_message, build_update_client_payload};
use crate::traits::message::CosmosMessage;
use crate::types::channel::{
    CosmosChannelOpenInitEvent, CosmosChannelOpenTryEvent, CosmosInitChannelOptions,
};
use crate::types::client::{
    CosmosCreateClientEvent, CosmosCreateClientPayload, CosmosUpdateClientPayload,
};
use crate::types::connection::{
    CosmosConnectionOpenInitEvent, CosmosConnectionOpenTryEvent, CosmosInitConnectionOptions,
};
use crate::types::error::{BaseError, Error};
use crate::types::payloads::channel::{
    CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenTryPayload,
};
use crate::types::payloads::connection::{
    CosmosConnectionOpenAckPayload, CosmosConnectionOpenConfirmPayload,
    CosmosConnectionOpenInitPayload, CosmosConnectionOpenTryPayload,
};
use crate::types::payloads::packet::{
    CosmosAckPacketPayload, CosmosReceivePacketPayload, CosmosTimeoutUnorderedPacketPayload,
};
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

    type Message = Arc<dyn CosmosMessage>;

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

    type ReceivePacketPayload = CosmosReceivePacketPayload;

    type AckPacketPayload = CosmosAckPacketPayload;

    type TimeoutUnorderedPacketPayload = CosmosTimeoutUnorderedPacketPayload;
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

    fn increment_height(height: &Height) -> Result<Height, Error> {
        Ok(height.increment())
    }

    fn estimate_message_size(message: &Arc<dyn CosmosMessage>) -> Result<usize, Error> {
        let raw = message
            .encode_protobuf(&Signer::dummy())
            .map_err(BaseError::encode)?;

        Ok(raw.encoded_len())
    }

    fn chain_status_height(status: &ChainStatus) -> &Height {
        &status.height
    }

    fn chain_status_timestamp(status: &ChainStatus) -> &Timestamp {
        &status.timestamp
    }

    fn try_extract_write_acknowledgement_event(
        event: &Arc<AbciEvent>,
    ) -> Option<WriteAcknowledgement> {
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

    fn try_extract_send_packet_event(event: &Arc<AbciEvent>) -> Option<SendPacket> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::SendPacket = event_type {
            let (packet, _) = extract_packet_and_write_ack_from_tx(event).ok()?;

            let send_packet_event = SendPacket { packet };

            Some(send_packet_event)
        } else {
            None
        }
    }

    fn extract_packet_from_send_packet_event(event: &SendPacket) -> Packet {
        event.packet.clone()
    }

    fn extract_packet_from_write_acknowledgement_event(ack: &WriteAcknowledgement) -> &Packet {
        &ack.packet
    }

    fn try_extract_create_client_event(event: Arc<AbciEvent>) -> Option<CosmosCreateClientEvent> {
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

    fn create_client_event_client_id(event: &CosmosCreateClientEvent) -> &ClientId {
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
        event: Arc<AbciEvent>,
    ) -> Option<CosmosConnectionOpenTryEvent> {
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
        event: &CosmosConnectionOpenTryEvent,
    ) -> &ConnectionId {
        &event.connection_id
    }

    fn try_extract_channel_open_init_event(
        event: Arc<AbciEvent>,
    ) -> Option<CosmosChannelOpenInitEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenInitChannel = event_type {
            let open_init_event = channel_open_init_try_from_abci_event(&event).ok()?;

            let channel_id = open_init_event.channel_id()?.clone();

            Some(CosmosChannelOpenInitEvent { channel_id })
        } else {
            None
        }
    }

    fn channel_open_try_event_channel_id(event: &CosmosChannelOpenTryEvent) -> &ChannelId {
        &event.channel_id
    }

    fn try_extract_channel_open_try_event(
        event: Arc<AbciEvent>,
    ) -> Option<CosmosChannelOpenTryEvent> {
        let event_type = event.kind.parse().ok()?;

        if let IbcEventType::OpenTryChannel = event_type {
            let open_try_event = channel_open_try_try_from_abci_event(&event).ok()?;

            let channel_id = open_try_event.channel_id()?.clone();

            Some(CosmosChannelOpenTryEvent { channel_id })
        } else {
            None
        }
    }

    fn channel_open_init_event_channel_id(event: &CosmosChannelOpenInitEvent) -> &ChannelId {
        &event.channel_id
    }

    fn chain_id(&self) -> &ChainId {
        &self.chain_id
    }

    async fn send_messages(
        &self,
        messages: Vec<Arc<dyn CosmosMessage>>,
    ) -> Result<Vec<Vec<Arc<AbciEvent>>>, Error> {
        let events = self.tx_context.send_messages(messages).await?;

        Ok(events)
    }

    async fn query_chain_status(&self) -> Result<ChainStatus, Error> {
        query_chain_status(self).await
    }

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Height, Arc<AbciEvent>)>> {
        &self.subscription
    }

    async fn query_write_acknowledgement_event(
        &self,
        packet: &Packet,
    ) -> Result<Option<WriteAcknowledgement>, Error> {
        query_write_acknowledgement_event(self, packet).await
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
        ReceivePacketPayload = CosmosReceivePacketPayload,
        AckPacketPayload = CosmosAckPacketPayload,
        TimeoutUnorderedPacketPayload = CosmosTimeoutUnorderedPacketPayload,
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

    fn client_state_latest_height(client_state: &ClientState) -> &Height {
        &client_state.latest_height
    }

    fn log_incoming_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn log_outgoing_packet(packet: &Packet) -> LogValue<'_> {
        LogValue::Display(packet)
    }

    fn counterparty_message_height_for_update_client(
        message: &Arc<dyn CosmosMessage>,
    ) -> Option<Height> {
        message.counterparty_message_height_for_update_client()
    }

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<ChainId, Error> {
        query_chain_id_from_channel_id(self, channel_id, port_id).await
    }

    async fn query_client_state(&self, client_id: &ClientId) -> Result<ClientState, Error> {
        query_client_state(self, client_id).await
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<ConsensusState, Error> {
        query_consensus_state(self, client_id, height).await
    }

    async fn query_is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Error> {
        query_is_packet_received(self, port_id, channel_id, sequence).await
    }

    /// Query the sequences of the packets that the chain has committed to be
    /// sent to the counterparty chain, of which the full packet relaying is not
    /// yet completed. Once the chain receives the ack from the counterparty
    /// chain, a given sequence should be removed from the packet commitment list.
    async fn query_packet_commitments(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        query_packet_commitments(self, channel_id, port_id).await
    }

    /// Given a list of counterparty commitment sequences,
    /// return a filtered list of sequences which the chain
    /// has not received the packet from the counterparty chain.
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        sequences: &[Sequence],
    ) -> Result<Vec<Sequence>, Self::Error> {
        query_unreceived_packet_sequences(self, channel_id, port_id, sequences).await
    }

    /// Given a list of sequences, a channel and port will query a list of outgoing
    /// packets which have not been relayed.
    async fn query_unreceived_packets(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_port_id: &PortId,
        sequences: &[Sequence],
        // The height is given to query the packets from a specific height.
        // This height should be the same as the query height from the
        // `CanQueryPacketCommitments` made on the same chain.
        height: &Height,
    ) -> Result<Vec<Packet>, Self::Error> {
        query_unreceived_packets(
            self,
            channel_id,
            port_id,
            counterparty_channel_id,
            counterparty_port_id,
            sequences,
            height,
        )
        .await
    }

    /// Construct a receive packet to be sent to a destination Cosmos
    /// chain from a source Cosmos chain.
    async fn build_receive_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosReceivePacketPayload, Error> {
        build_receive_packet_payload(self, height, packet).await
    }

    async fn build_receive_packet_message(
        &self,
        payload: CosmosReceivePacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_receive_packet_message(payload)
    }

    /// Construct an acknowledgement packet to be sent from a Cosmos
    /// chain that successfully received a packet from another Cosmos
    /// chain.
    async fn build_ack_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
        ack: &WriteAcknowledgement,
    ) -> Result<CosmosAckPacketPayload, Error> {
        build_ack_packet_payload(self, height, packet, ack).await
    }

    async fn build_ack_packet_message(
        &self,
        payload: CosmosAckPacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_ack_packet_message(payload)
    }

    /// Construct a timeout packet message to be sent between Cosmos chains
    /// over an unordered channel in the event that a packet that originated
    /// from a source chain was not received.
    async fn build_timeout_unordered_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosTimeoutUnorderedPacketPayload, Error> {
        build_timeout_unordered_packet_payload(self, height, packet).await
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        payload: CosmosTimeoutUnorderedPacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_timeout_unordered_packet_message(payload)
    }

    async fn build_create_client_payload(
        &self,
        client_settings: &ClientSettings,
    ) -> Result<CosmosCreateClientPayload, Error> {
        build_create_client_payload(self, client_settings).await
    }

    async fn build_create_client_message(
        &self,
        payload: CosmosCreateClientPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_create_client_message(payload)
    }

    async fn build_update_client_payload(
        &self,
        trusted_height: &Height,
        target_height: &Height,
        client_state: ClientState,
    ) -> Result<CosmosUpdateClientPayload, Error> {
        build_update_client_payload(self, trusted_height, target_height, client_state).await
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        payload: CosmosUpdateClientPayload,
    ) -> Result<Vec<Arc<dyn CosmosMessage>>, Error> {
        build_update_client_message(client_id, payload)
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, Error> {
        find_consensus_state_height_before(self, client_id, target_height).await
    }

    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<CosmosConnectionOpenInitPayload, Error> {
        build_connection_open_init_payload(self).await
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenTryPayload, Error> {
        build_connection_open_try_payload(self, height, client_id, connection_id).await
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenAckPayload, Error> {
        build_connection_open_ack_payload(self, height, client_id, connection_id).await
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenConfirmPayload, Error> {
        build_connection_open_confirm_payload(self, height, client_id, connection_id).await
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &CosmosInitConnectionOptions,
        counterparty_payload: CosmosConnectionOpenInitPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_connection_open_init_message(
            self,
            client_id,
            counterparty_client_id,
            init_connection_options,
            counterparty_payload,
        )
        .await
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenTryPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_connection_open_try_message(
            client_id,
            counterparty_client_id,
            counterparty_connection_id,
            counterparty_payload,
        )
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenAckPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_connection_open_ack_message(
            connection_id,
            counterparty_connection_id,
            counterparty_payload,
        )
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenConfirmPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_connection_open_confirm_message(connection_id, counterparty_payload)
    }

    async fn build_channel_open_try_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<CosmosChannelOpenTryPayload, Error> {
        build_channel_open_try_payload(self, height, port_id, channel_id).await
    }

    async fn build_channel_open_ack_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<CosmosChannelOpenAckPayload, Error> {
        build_channel_open_ack_payload(self, height, port_id, channel_id).await
    }

    async fn build_channel_open_confirm_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<CosmosChannelOpenConfirmPayload, Error> {
        build_channel_open_confirm_payload(self, height, port_id, channel_id).await
    }

    async fn build_channel_open_init_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        init_channel_options: &CosmosInitChannelOptions,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_channel_open_init_message(port_id, counterparty_port_id, init_channel_options)
    }

    async fn build_channel_open_try_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenTryPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_channel_open_try_message(
            port_id,
            counterparty_port_id,
            counterparty_channel_id,
            counterparty_payload,
        )
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenAckPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_channel_open_ack_message(
            port_id,
            channel_id,
            counterparty_channel_id,
            counterparty_payload,
        )
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenConfirmPayload,
    ) -> Result<Arc<dyn CosmosMessage>, Error> {
        build_channel_open_confirm_message(port_id, channel_id, counterparty_payload)
    }
}
