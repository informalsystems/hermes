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
use ibc_relayer_cosmos::traits::message::{CosmosMessage, ToCosmosMessage};
use ibc_relayer_cosmos::types::channel::CosmosInitChannelOptions;
use ibc_relayer_cosmos::types::error::{BaseError as CosmosBaseError, Error as CosmosError};
use ibc_relayer_cosmos::types::messages::channel::open_ack::CosmosChannelOpenAckMessage;
use ibc_relayer_cosmos::types::messages::channel::open_confirm::CosmosChannelOpenConfirmMessage;
use ibc_relayer_cosmos::types::messages::channel::open_init::CosmosChannelOpenInitMessage;
use ibc_relayer_cosmos::types::messages::channel::open_try::CosmosChannelOpenTryMessage;
use ibc_relayer_cosmos::types::messages::client::create::CosmosCreateClientMessage;
use ibc_relayer_cosmos::types::messages::client::update::CosmosUpdateClientMessage;
use ibc_relayer_cosmos::types::messages::connection::open_try::CosmosConnectionOpenTryMessage;
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
use ibc_relayer_types::core::ics03_connection::connection::State as ConnectionState;
use ibc_relayer_types::core::ics04_channel::channel::{
    ChannelEnd, Counterparty as ChannelCounterparty, State,
};
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics04_channel::timeout::TimeoutHeight;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::proofs::ConsensusProof;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height;

use crate::methods::encode::client_state::encode_client_state;
use crate::methods::encode::consensus_state::encode_consensus_state;
use crate::methods::encode::header::encode_header;
use crate::methods::encode::header_data::sign_header_data;
use crate::methods::encode::sign_data::sign_with_data;
use crate::methods::proofs::channel::channel_proof_data;
use crate::methods::proofs::client_state::client_state_proof_data;
use crate::methods::proofs::connection::connection_proof_data;
use crate::methods::proofs::consensus_state::consensus_state_proof_data;
use crate::traits::solomachine::SolomachineChain;
use crate::types::chain::SolomachineChainWrapper;
use crate::types::client_state::SolomachineClientState;
use crate::types::consensus_state::SolomachineConsensusState;
use crate::types::event::SolomachineEvent;
use crate::types::header::{SolomachineHeader, SolomachineHeaderData, SolomachineSignHeaderData};
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

    fn log_incoming_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        todo!()
    }

    fn log_outgoing_packet<'a>(event: &'a Packet) -> <Self::Logger as BaseLogger>::LogValue<'a> {
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

    fn client_state_latest_height(client_state: &SolomachineClientState) -> &Height {
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

    async fn build_receive_packet_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        packet: &Packet,
    ) -> Result<SolomachineReceivePacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_ack_packet_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        packet: &Packet,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<SolomachineAckPacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        packet: &Packet,
    ) -> Result<SolomachineTimeoutUnorderedPacketPayload, Chain::Error> {
        todo!()
    }

    async fn build_create_client_payload(
        &self,
        create_client_options: &(),
    ) -> Result<SolomachineCreateClientPayload, Chain::Error> {
        let public_key = *self.chain.public_key();
        let diversifier = self.chain.new_diversifier().await;
        let timestamp = self.chain.current_time();

        let consensus_state = SolomachineConsensusState {
            public_key,
            diversifier,
            timestamp,
        };

        let client_state = SolomachineClientState {
            sequence: 0,
            is_frozen: false,
            consensus_state,
        };

        let payload = SolomachineCreateClientPayload { client_state };

        Ok(payload)
    }

    async fn build_update_client_payload(
        &self,
        trusted_height: &Height,
        target_height: &Height,
        client_state: SolomachineClientState,
    ) -> Result<SolomachineUpdateClientPayload, Chain::Error> {
        // TODO: check that the public key is the same in the consensus state.
        // We currently only support updating the diversifier but not the public key.

        let public_key = self.chain.public_key();
        let current_diversifier = &client_state.consensus_state.diversifier;

        let next_diversifier = self.chain.next_diversifier(current_diversifier).await;

        // TODO: check that current time is greater than or equal to the consensus state time.
        let timestamp = self.chain.current_time();

        let header_data = SolomachineHeaderData {
            new_public_key: *public_key,
            new_diversifier: next_diversifier,
        };

        let sign_data = SolomachineSignHeaderData {
            header_data,
            sequence: client_state.sequence,
            timestamp,
            diversifier: current_diversifier.clone(),
        };

        let secret_key = self.chain.secret_key();

        let signature = sign_header_data(secret_key, &sign_data).map_err(Chain::encode_error)?;

        let header = SolomachineHeader {
            timestamp,
            signature,
            header_data: sign_data.header_data,
        };

        let payload = SolomachineUpdateClientPayload { header };

        Ok(payload)
    }

    async fn build_connection_open_init_payload(
        &self,
        _client_state: &SolomachineClientState,
    ) -> Result<SolomachineConnectionOpenInitPayload, Chain::Error> {
        let commitment_prefix = self.chain.commitment_prefix();

        let payload = SolomachineConnectionOpenInitPayload {
            commitment_prefix: commitment_prefix.to_string(),
        };

        Ok(payload)
    }

    async fn build_connection_open_try_payload(
        &self,
        solo_client_state: &SolomachineClientState,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<SolomachineConnectionOpenTryPayload, Chain::Error> {
        let connection = self.chain.query_connection(connection_id).await?;

        if connection.state != ConnectionState::Init {
            return Err(Chain::invalid_connection_state_error(
                ConnectionState::Init,
                connection.state,
            ));
        }

        let versions = connection.versions().to_vec();

        let delay_period = connection.delay_period();

        let commitment_prefix = self.chain.commitment_prefix();

        let connection_data = connection_proof_data(
            solo_client_state,
            commitment_prefix,
            connection_id,
            connection,
        )
        .map_err(Chain::encode_error)?;

        let cosmos_client_state = self.chain.query_client_state(client_id).await?;

        let client_state_data = client_state_proof_data(
            solo_client_state,
            commitment_prefix,
            client_id,
            &cosmos_client_state,
        )
        .map_err(Chain::encode_error)?;

        let cosmos_consensus_state = self.chain.query_consensus_state(client_id, *height).await?;

        let consensus_state_data = consensus_state_proof_data(
            solo_client_state,
            commitment_prefix,
            client_id,
            *height,
            &cosmos_consensus_state,
        )
        .map_err(Chain::encode_error)?;

        let secret_key = self.chain.secret_key();

        let connection_proof =
            sign_with_data(secret_key, &connection_data).map_err(Chain::encode_error)?;

        let client_state_proof =
            sign_with_data(secret_key, &client_state_data).map_err(Chain::encode_error)?;

        let consensus_state_proof =
            sign_with_data(secret_key, &consensus_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineConnectionOpenTryPayload {
            commitment_prefix: commitment_prefix.to_string(),
            client_state: cosmos_client_state,
            versions,
            delay_period,
            update_height: *height,
            proof_init: connection_proof,
            proof_client: client_state_proof,
            proof_consensus: consensus_state_proof,
        };

        Ok(payload)
    }

    async fn build_connection_open_ack_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        client_id: &ClientId,
        connection_id: &ConnectionId,
    ) -> Result<SolomachineConnectionOpenAckPayload, Chain::Error> {
        let connection = self.chain.query_connection(connection_id).await?;

        if connection.state != ConnectionState::TryOpen {
            return Err(Chain::invalid_connection_state_error(
                ConnectionState::TryOpen,
                connection.state,
            ));
        }

        let version = connection
            .versions()
            .iter()
            .next()
            .cloned()
            .unwrap_or_default();

        let commitment_prefix = self.chain.commitment_prefix();

        let cosmos_client_state = self.chain.query_client_state(client_id).await?;

        let client_state_data = client_state_proof_data(
            client_state,
            commitment_prefix,
            client_id,
            &cosmos_client_state,
        )
        .map_err(Chain::encode_error)?;

        let connection_data =
            connection_proof_data(client_state, commitment_prefix, connection_id, connection)
                .map_err(Chain::encode_error)?;

        let cosmos_consensus_state = self.chain.query_consensus_state(client_id, *height).await?;

        let consensus_state_data = consensus_state_proof_data(
            client_state,
            commitment_prefix,
            client_id,
            *height,
            &cosmos_consensus_state,
        )
        .map_err(Chain::encode_error)?;

        let secret_key = self.chain.secret_key();

        let connection_proof =
            sign_with_data(secret_key, &connection_data).map_err(Chain::encode_error)?;

        let client_state_proof =
            sign_with_data(secret_key, &client_state_data).map_err(Chain::encode_error)?;

        let consensus_state_proof =
            sign_with_data(secret_key, &consensus_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineConnectionOpenAckPayload {
            client_state: cosmos_client_state,
            version,
            update_height: *height,
            proof_try: connection_proof,
            proof_client: client_state_proof,
            proof_consensus: consensus_state_proof,
        };

        Ok(payload)
    }

    async fn build_connection_open_confirm_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        client_id: &ClientId,
        _connection_id: &ConnectionId,
    ) -> Result<SolomachineConnectionOpenConfirmPayload, Chain::Error> {
        let secret_key = self.chain.secret_key();
        let commitment_prefix = self.chain.commitment_prefix();
        let cosmos_client_state = self.chain.query_client_state(client_id).await?;

        let client_state_data = client_state_proof_data(
            client_state,
            commitment_prefix,
            client_id,
            &cosmos_client_state,
        )
        .map_err(Chain::encode_error)?;

        let connection_proof =
            sign_with_data(secret_key, &client_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineConnectionOpenConfirmPayload {
            update_height: *height,
            proof_ack: connection_proof,
        };

        Ok(payload)
    }

    async fn build_channel_open_try_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<SolomachineChannelOpenTryPayload, Chain::Error> {
        let channel = self.chain.query_channel(channel_id, port_id).await?;

        if channel.state != State::Init {
            return Err(Chain::invalid_channel_state_error(
                State::Init,
                channel.state,
            ));
        }

        let ordering = *channel.ordering();
        let connection_hops = channel.connection_hops().clone();
        let version = channel.version().clone();

        let commitment_prefix = self.chain.commitment_prefix();

        let channel_state_data =
            channel_proof_data(client_state, commitment_prefix, channel_id, channel)
                .map_err(Chain::encode_error)?;

        let secret_key = self.chain.secret_key();

        let channel_proof =
            sign_with_data(secret_key, &channel_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineChannelOpenTryPayload {
            ordering,
            connection_hops,
            version,
            update_height: *height,
            proof_init: channel_proof,
        };

        Ok(payload)
    }

    async fn build_channel_open_ack_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<SolomachineChannelOpenAckPayload, Chain::Error> {
        let channel = self.chain.query_channel(channel_id, port_id).await?;

        if channel.state != State::TryOpen {
            return Err(Chain::invalid_channel_state_error(
                State::TryOpen,
                channel.state,
            ));
        }

        let version = channel.version().clone();

        let commitment_prefix = self.chain.commitment_prefix();

        let channel_state_data =
            channel_proof_data(client_state, commitment_prefix, channel_id, channel)
                .map_err(Chain::encode_error)?;

        let secret_key = self.chain.secret_key();

        let channel_proof =
            sign_with_data(secret_key, &channel_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineChannelOpenAckPayload {
            version,
            update_height: *height,
            proof_try: channel_proof,
        };

        Ok(payload)
    }

    async fn build_channel_open_confirm_payload(
        &self,
        client_state: &SolomachineClientState,
        height: &Height,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<SolomachineChannelOpenConfirmPayload, Chain::Error> {
        let channel = self.chain.query_channel(channel_id, port_id).await?;

        if channel.state != State::Open {
            return Err(Chain::invalid_channel_state_error(
                State::Open,
                channel.state,
            ));
        }

        let commitment_prefix = self.chain.commitment_prefix();

        let channel_state_data =
            channel_proof_data(client_state, commitment_prefix, channel_id, channel)
                .map_err(Chain::encode_error)?;

        let secret_key = self.chain.secret_key();

        let channel_proof =
            sign_with_data(secret_key, &channel_state_data).map_err(Chain::encode_error)?;

        let payload = SolomachineChannelOpenConfirmPayload {
            update_height: *height,
            proof_ack: channel_proof,
        };

        Ok(payload)
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

    fn counterparty_message_height_for_update_client(
        message: &SolomachineMessage,
    ) -> Option<Height> {
        // No need to update client as we are trusting the Cosmos full node,
        // and rely directly on the full node for detecting misbehavior.
        None
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
        self.chain.query_client_state(client_id).await
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<TendermintConsensusState, Chain::Error> {
        self.chain.query_consensus_state(client_id, *height).await
    }

    async fn query_is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, Chain::Error> {
        todo!()
    }

    async fn query_packet_commitments(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<(Vec<Sequence>, Height), Chain::Error> {
        todo!()
    }

    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        sequences: &[Sequence],
    ) -> Result<Vec<Sequence>, Chain::Error> {
        todo!()
    }

    async fn query_send_packets_from_sequences(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_port_id: &PortId,
        sequences: &[Sequence],
        height: &Height,
    ) -> Result<Vec<Packet>, Chain::Error> {
        todo!()
    }

    async fn build_receive_packet_message(
        &self,
        packet: &Packet,
        payload: CosmosReceivePacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_ack_packet_message(
        &self,
        packet: &Packet,
        payload: CosmosAckPacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        packet: &Packet,
        counterparty_payload: CosmosTimeoutUnorderedPacketPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        todo!()
    }

    async fn build_create_client_message(
        &self,
        counterparty_payload: CosmosCreateClientPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosCreateClient(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        counterparty_payload: CosmosUpdateClientPayload,
    ) -> Result<Vec<SolomachineMessage>, Chain::Error> {
        let message = SolomachineMessage::CosmosUpdateClient(Box::new(counterparty_payload));

        Ok(vec![message])
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, Chain::Error> {
        todo!()
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: CosmosConnectionOpenInitPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosConnectionOpenInit(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenTryPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosConnectionOpenTry(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenAckPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosConnectionOpenAck(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: CosmosConnectionOpenConfirmPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message =
            SolomachineMessage::CosmosConnectionOpenConfirm(Box::new(counterparty_payload));

        Ok(message)
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
        let message = SolomachineMessage::CosmosChannelOpenTry(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenAckPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosChannelOpenAck(Box::new(counterparty_payload));

        Ok(message)
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: CosmosChannelOpenConfirmPayload,
    ) -> Result<SolomachineMessage, Chain::Error> {
        let message = SolomachineMessage::CosmosChannelOpenConfirm(Box::new(counterparty_payload));

        Ok(message)
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

    fn counterparty_message_height_for_update_client(
        message: &Arc<dyn CosmosMessage>,
    ) -> Option<Height> {
        message.counterparty_message_height_for_update_client()
    }

    async fn query_chain_id_from_channel_id(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<ChainId, CosmosError> {
        todo!()
    }

    async fn query_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<SolomachineClientState, CosmosError> {
        todo!()
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<SolomachineConsensusState, CosmosError> {
        todo!()
    }

    async fn find_consensus_state_height_before(
        &self,
        client_id: &ClientId,
        target_height: &Height,
    ) -> Result<Height, CosmosError> {
        todo!()
    }

    async fn query_is_packet_received(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<bool, CosmosError> {
        todo!()
    }

    async fn query_packet_commitments(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
    ) -> Result<(Vec<Sequence>, Height), CosmosError> {
        todo!()
    }

    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        sequences: &[Sequence],
    ) -> Result<Vec<Sequence>, CosmosError> {
        todo!()
    }

    async fn query_send_packets_from_sequences(
        &self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_port_id: &PortId,
        sequences: &[Sequence],
        height: &Height,
    ) -> Result<Vec<Packet>, CosmosError> {
        todo!()
    }

    async fn build_receive_packet_message(
        &self,
        packet: &Packet,
        payload: SolomachineReceivePacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_ack_packet_message(
        &self,
        packet: &Packet,
        payload: SolomachineAckPacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_timeout_unordered_packet_message(
        &self,
        packet: &Packet,
        payload: SolomachineTimeoutUnorderedPacketPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_create_client_message(
        &self,
        counterparty_payload: SolomachineCreateClientPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let client_state = encode_client_state(&counterparty_payload.client_state)
            .map_err(CosmosBaseError::encode)?;

        let consensus_state =
            encode_consensus_state(&counterparty_payload.client_state.consensus_state)
                .map_err(CosmosBaseError::encode)?;

        let message = CosmosCreateClientMessage {
            client_state,
            consensus_state,
        };

        Ok(message.to_cosmos_message())
    }

    async fn build_update_client_message(
        &self,
        client_id: &ClientId,
        payload: SolomachineUpdateClientPayload,
    ) -> Result<Vec<Arc<dyn CosmosMessage>>, CosmosError> {
        let header = encode_header(&payload.header).map_err(CosmosBaseError::encode)?;

        let message = CosmosUpdateClientMessage {
            client_id: client_id.clone(),
            header,
        };

        Ok(vec![message.to_cosmos_message()])
    }

    async fn build_connection_open_init_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: SolomachineConnectionOpenInitPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &ClientId,
        counterparty_client_id: &ClientId,
        counterparty_connection_id: &ConnectionId,
        payload: SolomachineConnectionOpenTryPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let counterparty_commitment_prefix = Vec::from(payload.commitment_prefix)
            .try_into()
            .map_err(CosmosBaseError::ics23)?;

        let proof_init = Vec::from(payload.proof_init.serialize_compact())
            .try_into()
            .map_err(CosmosBaseError::proofs)?;

        let proof_client: ibc_relayer_types::core::ics23_commitment::commitment::CommitmentProofBytes = Vec::from(payload.proof_client.serialize_compact()).try_into()
            .map_err(CosmosBaseError::proofs)?;

        let consensus_signature = Vec::from(payload.proof_consensus.serialize_compact())
            .try_into()
            .map_err(CosmosBaseError::proofs)?;

        let proof_consensus = ConsensusProof::new(consensus_signature, payload.update_height)
            .map_err(CosmosBaseError::proofs)?;

        let message = CosmosConnectionOpenTryMessage {
            client_id: client_id.clone(),
            counterparty_client_id: counterparty_client_id.clone(),
            counterparty_connection_id: counterparty_connection_id.clone(),
            counterparty_commitment_prefix,
            counterparty_versions: payload.versions,
            delay_period: payload.delay_period,
            client_state: payload.client_state.into(),
            update_height: payload.update_height,
            proof_init,
            proof_client,
            proof_consensus,
        };

        Ok(message.to_cosmos_message())
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_connection_id: &ConnectionId,
        counterparty_payload: SolomachineConnectionOpenAckPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &ConnectionId,
        counterparty_payload: SolomachineConnectionOpenConfirmPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        todo!()
    }

    async fn build_channel_open_init_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        init_channel_options: &CosmosInitChannelOptions,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let ordering = init_channel_options.ordering;
        let connection_hops = init_channel_options.connection_hops.clone();
        let channel_version = init_channel_options.channel_version.clone();
        let counterparty = ChannelCounterparty::new(counterparty_port_id.clone(), None);

        let channel = ChannelEnd::new(
            State::Init,
            ordering,
            counterparty,
            connection_hops,
            channel_version,
        );

        let message = CosmosChannelOpenInitMessage {
            port_id: port_id.clone(),
            channel,
        };

        Ok(message.to_cosmos_message())
    }

    async fn build_channel_open_try_message(
        &self,
        port_id: &PortId,
        counterparty_port_id: &PortId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenTryPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let proof_init = Vec::from(counterparty_payload.proof_init.serialize_compact())
            .try_into()
            .map_err(CosmosBaseError::proofs)?;

        let counterparty = ChannelCounterparty::new(
            counterparty_port_id.clone(),
            Some(counterparty_channel_id.clone()),
        );

        let channel = ChannelEnd::new(
            State::TryOpen,
            counterparty_payload.ordering,
            counterparty,
            counterparty_payload.connection_hops,
            counterparty_payload.version.clone(),
        );

        let message = CosmosChannelOpenTryMessage {
            port_id: port_id.clone(),
            channel,
            counterparty_version: counterparty_payload.version,
            update_height: counterparty_payload.update_height,
            proof_init,
        };

        Ok(message.to_cosmos_message())
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenAckPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let proof_try = Vec::from(counterparty_payload.proof_try.serialize_compact())
            .try_into()
            .map_err(CosmosBaseError::proofs)?;

        let message = CosmosChannelOpenAckMessage {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            counterparty_channel_id: counterparty_channel_id.clone(),
            counterparty_version: counterparty_payload.version,
            update_height: counterparty_payload.update_height,
            proof_try,
        };

        Ok(message.to_cosmos_message())
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        counterparty_payload: SolomachineChannelOpenConfirmPayload,
    ) -> Result<Arc<dyn CosmosMessage>, CosmosError> {
        let proof_ack = Vec::from(counterparty_payload.proof_ack.serialize_compact())
            .try_into()
            .map_err(CosmosBaseError::proofs)?;

        let message = CosmosChannelOpenConfirmMessage {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            update_height: counterparty_payload.update_height,
            proof_ack,
        };

        Ok(message.to_cosmos_message())
    }
}
