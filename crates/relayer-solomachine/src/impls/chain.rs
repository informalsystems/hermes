use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer::chain::endpoint::ChainStatus;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_all_in_one::one_for_all::traits::chain::{OfaChain, OfaChainTypes, OfaIbcChain};
use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_components::logger::traits::logger::BaseLogger;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_cosmos::contexts::chain::CosmosChain;
use ibc_relayer_cosmos::types::payloads::channel::{
    CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenTryPayload,
};
use ibc_relayer_cosmos::types::payloads::client::{
    CosmosCreateClientPayload, CosmosUpdateClientPayload,
};
use ibc_relayer_cosmos::types::payloads::connection::{
    CosmosConnectionOpenAckPayload, CosmosConnectionOpenConfirmPayload,
    CosmosConnectionOpenInitPayload, CosmosConnectionOpenTryPayload,
};
use ibc_relayer_cosmos::types::payloads::packet::{
    CosmosAckPacketPayload, CosmosReceivePacketPayload, CosmosTimeoutUnorderedPacketPayload,
};
use ibc_relayer_cosmos::types::telemetry::CosmosTelemetry;
use ibc_relayer_cosmos::types::tendermint::{TendermintClientState, TendermintConsensusState};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;

use crate::traits::solomachine::SolomachineChain;
use crate::types::chain::SolomachineChainWrapper;
use crate::types::client_state::SolomachineClientState;
use crate::types::consensus_state::SolomachineConsensusState;
use crate::types::event::SolomachineEvent;
use crate::types::message::SolomachineMessage;
use crate::types::payloads::channel::{
    SolomachineChannelOpenAckPayload, SolomachineChannelOpenConfirmPayload,
    SolomachineChannelOpenTryPayload,
};
use crate::types::payloads::client::{
    SolomachineCreateClientPayload, SolomachineUpdateClientPayload,
};
use crate::types::payloads::connection::{
    SolomachineConnectionOpenAckPayload, SolomachineConnectionOpenConfirmPayload,
    SolomachineConnectionOpenInitPayload, SolomachineConnectionOpenTryPayload,
};
use crate::types::payloads::packet::{
    SolomachineAckPacketPayload, SolomachineReceivePacketPayload,
    SolomachineTimeoutUnorderedPacketPayload,
};

impl<Chain> OfaChainTypes for SolomachineChainWrapper<Chain>
where
    Chain: SolomachineChain,
{
    type Error = Chain::Error;

    type Runtime = Chain::Runtime;

    type Logger = Chain::Logger;

    type Telemetry = CosmosTelemetry;

    type Message = SolomachineMessage;

    type Event = SolomachineEvent;

    type ClientState = SolomachineClientState;

    type ConsensusState = SolomachineConsensusState;

    type Height = Height;

    type Timestamp = Timestamp;

    type ChainId = ChainId;

    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type ChainStatus = ChainStatus;

    type IncomingPacket = Packet;

    type OutgoingPacket = Packet;

    type ConnectionDetails = ();

    type ConnectionVersion = ();

    type CreateClientPayloadOptions = ();

    type InitConnectionOptions = ();

    type InitChannelOptions = ();

    type CreateClientPayload = SolomachineCreateClientPayload;

    type UpdateClientPayload = SolomachineUpdateClientPayload;

    type ConnectionOpenInitPayload = SolomachineConnectionOpenInitPayload;

    type ConnectionOpenTryPayload = SolomachineConnectionOpenTryPayload;

    type ConnectionOpenAckPayload = SolomachineConnectionOpenAckPayload;

    type ConnectionOpenConfirmPayload = SolomachineConnectionOpenConfirmPayload;

    type ChannelOpenTryPayload = SolomachineChannelOpenTryPayload;

    type ChannelOpenAckPayload = SolomachineChannelOpenAckPayload;

    type ChannelOpenConfirmPayload = SolomachineChannelOpenConfirmPayload;

    type ReceivePacketPayload = SolomachineReceivePacketPayload;

    type AckPacketPayload = SolomachineAckPacketPayload;

    type TimeoutUnorderedPacketPayload = SolomachineTimeoutUnorderedPacketPayload;

    type CreateClientEvent = ();

    type ConnectionOpenInitEvent = ();

    type ConnectionOpenTryEvent = ();

    type ChannelOpenInitEvent = ();

    type ChannelOpenTryEvent = ();

    type SendPacketEvent = ();

    type WriteAcknowledgementEvent = ();
}

#[allow(unused_variables)]
#[async_trait]
impl<Chain> OfaChain for SolomachineChainWrapper<Chain>
where
    Chain: SolomachineChain,
{
    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        todo!()
    }

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Chain::Error {
        todo!()
    }

    fn logger(&self) -> &Self::Logger {
        todo!()
    }

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry> {
        todo!()
    }

    fn log_event<'a>(event: &'a Self::Event) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn increment_height(height: &Height) -> Result<Height, Chain::Error> {
        todo!()
    }

    fn estimate_message_size(message: &SolomachineMessage) -> Result<usize, Chain::Error> {
        todo!()
    }

    fn chain_status_height(status: &Self::ChainStatus) -> &Height {
        todo!()
    }

    fn chain_status_timestamp(status: &Self::ChainStatus) -> &Timestamp {
        todo!()
    }

    fn try_extract_write_acknowledgement_event(
        event: &Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        todo!()
    }

    fn try_extract_send_packet_event(event: &Self::Event) -> Option<Self::SendPacketEvent> {
        todo!()
    }

    fn extract_packet_from_send_packet_event(event: &Self::SendPacketEvent) -> Packet {
        todo!()
    }

    fn extract_packet_from_write_acknowledgement_event(
        ack: &Self::WriteAcknowledgementEvent,
    ) -> &Packet {
        todo!()
    }

    fn try_extract_create_client_event(event: Self::Event) -> Option<Self::CreateClientEvent> {
        todo!()
    }

    fn create_client_event_client_id(event: &Self::CreateClientEvent) -> &ClientId {
        todo!()
    }

    fn try_extract_connection_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenInitEvent> {
        todo!()
    }

    fn connection_open_init_event_connection_id(
        event: &Self::ConnectionOpenInitEvent,
    ) -> &ConnectionId {
        todo!()
    }

    fn try_extract_connection_open_try_event(
        event: Self::Event,
    ) -> Option<Self::ConnectionOpenTryEvent> {
        todo!()
    }

    fn connection_open_try_event_connection_id(
        event: &Self::ConnectionOpenTryEvent,
    ) -> &ConnectionId {
        todo!()
    }

    fn try_extract_channel_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ChannelOpenInitEvent> {
        todo!()
    }

    fn channel_open_init_event_channel_id(event: &Self::ChannelOpenInitEvent) -> &ChannelId {
        todo!()
    }

    fn try_extract_channel_open_try_event(event: Self::Event) -> Option<Self::ChannelOpenTryEvent> {
        todo!()
    }

    fn channel_open_try_event_channel_id(event: &Self::ChannelOpenTryEvent) -> &ChannelId {
        todo!()
    }

    async fn send_messages(
        &self,
        messages: Vec<SolomachineMessage>,
    ) -> Result<Vec<Vec<Self::Event>>, Chain::Error> {
        todo!()
    }

    fn chain_id(&self) -> &Self::ChainId {
        todo!()
    }

    async fn query_chain_status(&self) -> Result<Self::ChainStatus, Chain::Error> {
        todo!()
    }

    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Height, Self::Event)>> {
        todo!()
    }

    async fn query_write_acknowledgement_event(
        &self,
        packet: &Packet,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Chain::Error> {
        todo!()
    }
}

#[allow(unused_variables)]
#[async_trait]
impl<Chain, Counterparty> OfaIbcChain<CosmosChain<Counterparty>> for SolomachineChainWrapper<Chain>
where
    Chain: SolomachineChain,
    Counterparty: ChainHandle,
{
    fn incoming_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn incoming_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn incoming_packet_src_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn incoming_packet_dst_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn incoming_packet_sequence(packet: &Packet) -> &Sequence {
        todo!()
    }

    fn incoming_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        todo!()
    }

    fn incoming_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        todo!()
    }

    fn outgoing_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn outgoing_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn outgoing_packet_src_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn outgoing_packet_dst_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn outgoing_packet_sequence(packet: &Packet) -> &Sequence {
        todo!()
    }

    fn outgoing_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        todo!()
    }

    fn outgoing_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        todo!()
    }

    fn client_state_latest_height(client_state: &SolomachineClientState) -> &Height {
        todo!()
    }

    fn log_incoming_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn log_outgoing_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn counterparty_message_height_for_update_client(
        message: &SolomachineMessage,
    ) -> Option<Height> {
        todo!()
    }

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<ChainId, Chain::Error> {
        todo!()
    }

    async fn query_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<TendermintClientState, Chain::Error> {
        todo!()
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<TendermintConsensusState, Chain::Error> {
        todo!()
    }

    async fn query_is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Chain::Error> {
        todo!()
    }

    async fn build_receive_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<Self::ReceivePacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_receive_packet_message(
        &self,
        payload: CosmosReceivePacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_ack_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Self::AckPacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_ack_packet_message(
        &self,
        payload: CosmosAckPacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        payload: CosmosTimeoutUnorderedPacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_create_client_payload(
        &self,
        create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<Self::CreateClientPayload, Chain::Error> {
        todo!()
    }

    async fn build_create_client_message(
        &self,
        counterparty_payload: CosmosCreateClientPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_update_client_payload(
        &self,
        trusted_height: &Height,
        target_height: &Height,
        client_state: SolomachineClientState,
    ) -> Result<Self::UpdateClientPayload, Chain::Error> {
        todo!()
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        payload: CosmosUpdateClientPayload,
    ) -> Result<Vec<SolomachineMessage>, Chain::Error> {
        todo!()
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<Self::ConnectionOpenInitPayload, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: CosmosConnectionOpenInitPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenTryPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenAckPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenConfirmPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_try_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_ack_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Self::ChannelOpenAckPayload, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_confirm_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Self::ChannelOpenConfirmPayload, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_init_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_try_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenTryPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenAckPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenConfirmPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }
}

#[allow(unused_variables)]
#[async_trait]
impl<Chain, Counterparty> OfaIbcChain<SolomachineChainWrapper<Counterparty>> for CosmosChain<Chain>
where
    Counterparty: SolomachineChain,
    Chain: ChainHandle,
{
    fn incoming_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn incoming_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn incoming_packet_src_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn incoming_packet_dst_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn incoming_packet_sequence(packet: &Packet) -> &Sequence {
        todo!()
    }

    fn incoming_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        todo!()
    }

    fn incoming_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        todo!()
    }

    fn outgoing_packet_src_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn outgoing_packet_dst_channel_id(packet: &Packet) -> &ChannelId {
        todo!()
    }

    fn outgoing_packet_src_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn outgoing_packet_dst_port(packet: &Packet) -> &PortId {
        todo!()
    }

    fn outgoing_packet_sequence(packet: &Packet) -> &Sequence {
        todo!()
    }

    fn outgoing_packet_timeout_height(packet: &Packet) -> Option<&Height> {
        todo!()
    }

    fn outgoing_packet_timeout_timestamp(packet: &Packet) -> &Timestamp {
        todo!()
    }

    fn client_state_latest_height(client_state: &TendermintClientState) -> &Height {
        todo!()
    }

    fn log_incoming_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn log_outgoing_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn counterparty_message_height_for_update_client(message: &Self::Message) -> Option<Height> {
        todo!()
    }

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<ChainId, Self::Error> {
        todo!()
    }

    async fn query_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<SolomachineClientState, Self::Error> {
        todo!()
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<SolomachineConsensusState, Self::Error> {
        todo!()
    }

    async fn query_is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Self::Error> {
        todo!()
    }

    async fn build_receive_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosReceivePacketPayload, Self::Error> {
        todo!()
    }

    async fn build_receive_packet_message(
        &self,
        payload: SolomachineReceivePacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_ack_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<CosmosAckPacketPayload, Self::Error> {
        todo!()
    }

    async fn build_ack_packet_message(
        &self,
        payload: SolomachineAckPacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_payload(
        &self,
        height: &Height,
        packet: &Packet,
    ) -> Result<CosmosTimeoutUnorderedPacketPayload, Self::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        payload: SolomachineTimeoutUnorderedPacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_create_client_payload(
        &self,
        create_client_options: &Self::CreateClientPayloadOptions,
    ) -> Result<CosmosCreateClientPayload, Self::Error> {
        todo!()
    }

    async fn build_create_client_message(
        &self,
        counterparty_payload: SolomachineCreateClientPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_update_client_payload(
        &self,
        trusted_height: &Height,
        target_height: &Height,
        client_state: TendermintClientState,
    ) -> Result<CosmosUpdateClientPayload, Self::Error> {
        todo!()
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        payload: SolomachineUpdateClientPayload,
    ) -> Result<Vec<Self::Message>, Self::Error> {
        todo!()
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, Self::Error> {
        todo!()
    }

    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<CosmosConnectionOpenInitPayload, Self::Error> {
        todo!()
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenTryPayload, Self::Error> {
        todo!()
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenAckPayload, Self::Error> {
        todo!()
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<CosmosConnectionOpenConfirmPayload, Self::Error> {
        todo!()
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: SolomachineConnectionOpenInitPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: SolomachineConnectionOpenTryPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: SolomachineConnectionOpenAckPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: SolomachineConnectionOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_channel_open_try_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Self::Error> {
        todo!()
    }

    async fn build_channel_open_ack_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<CosmosChannelOpenAckPayload, Self::Error> {
        todo!()
    }

    async fn build_channel_open_confirm_payload(
        &self,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<CosmosChannelOpenConfirmPayload, Self::Error> {
        todo!()
    }

    async fn build_channel_open_init_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_channel_open_try_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenTryPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenAckPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error> {
        todo!()
    }
}
