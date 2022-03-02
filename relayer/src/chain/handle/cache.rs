use crossbeam_channel as channel;
use ibc::core::ics02_client::client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc::core::ics02_client::client_state::{AnyClientState, IdentifiedAnyClientState};
use ibc::core::ics02_client::events::UpdateClient;
use ibc::core::ics02_client::misbehaviour::MisbehaviourEvidence;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::query::QueryTxRequest;
use ibc::{
    core::ics02_client::header::AnyHeader,
    core::ics03_connection::connection::ConnectionEnd,
    core::ics03_connection::version::Version,
    core::ics04_channel::channel::ChannelEnd,
    core::ics23_commitment::commitment::CommitmentPrefix,
    core::ics24_host::identifier::{
        ChainId, ChannelId, ClientId, ConnectionId, PortChannelId, PortId,
    },
    events::IbcEvent,
    proofs::Proofs,
    query::QueryBlockRequest,
    signer::Signer,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryChannelClientStateRequest, QueryChannelsRequest,
    QueryConnectionChannelsRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::{QueryClientStatesRequest, QueryConsensusStatesRequest};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::core::connection::v1::QueryClientConnectionsRequest;
use ibc_proto::ibc::core::connection::v1::QueryConnectionsRequest;
use serde::{Serialize, Serializer};

use crate::cache::Cache;
use crate::chain::handle::{ChainHandle, ChainRequest, Subscription};
use crate::chain::tx::TrackedMsgs;
use crate::chain::{HealthCheck, StatusResponse};
use crate::config::ChainConfig;
use crate::error::Error;
use crate::{connection::ConnectionMsgType, keyring::KeyEntry};

#[derive(Debug, Clone)]
pub struct CachingChainHandle<Handle> {
    handle: Handle,
    cache: Cache,
}

impl<Handle> CachingChainHandle<Handle> {
    pub fn new(handle: Handle) -> Self {
        Self {
            handle,
            cache: Cache::new(),
        }
    }

    pub fn handle(&self) -> &Handle {
        &self.handle
    }
}

impl<Handle: Serialize> Serialize for CachingChainHandle<Handle> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.handle.serialize(serializer)
    }
}

impl<Handle: ChainHandle> ChainHandle for CachingChainHandle<Handle> {
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
        Self::new(Handle::new(chain_id, sender))
    }

    fn id(&self) -> ChainId {
        self.handle().id()
    }

    fn shutdown(&self) -> Result<(), Error> {
        self.handle().shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.handle().health_check()
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.handle().subscribe()
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        self.handle().send_messages_and_wait_commit(tracked_msgs)
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.handle().send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.handle().get_signer()
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.handle().config()
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.handle().get_key()
    }

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error> {
        self.handle().add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.handle().ibc_version()
    }

    fn query_status(&self) -> Result<StatusResponse, Error> {
        self.handle().query_status()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        let handle = self.handle();
        self.cache
            .get_or_try_update_latest_height_with(|| handle.query_latest_height())
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.handle().query_clients(request)
    }

    // TODO: Introduce new query_client_state_latest to separate from this one.
    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        let handle = self.handle();
        if height.is_zero() {
            self.cache
                .get_or_try_insert_client_state_with(client_id, || {
                    handle.query_client_state(client_id, height)
                })
        } else {
            handle.query_client_state(client_id, height)
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.handle().query_client_connections(request)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.handle().query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
    ) -> Result<AnyConsensusState, Error> {
        self.handle()
            .query_consensus_state(client_id, consensus_height, query_height)
    }

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.handle().query_upgraded_client_state(height)
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.handle().query_upgraded_consensus_state(height)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.handle().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.handle().query_compatible_versions()
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        let handle = self.handle();
        if height.is_zero() {
            self.cache
                .get_or_try_insert_connection_with(connection_id, || {
                    handle.query_connection(connection_id, height)
                })
        } else {
            handle.query_connection(connection_id, height)
        }
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.handle().query_connections(request)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.handle().query_connection_channels(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        self.handle().query_next_sequence_receive(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.handle().query_channels(request)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        let handle = self.handle();
        if height.is_zero() {
            self.cache.get_or_try_insert_channel_with(
                &PortChannelId::new(channel_id.clone(), port_id.clone()),
                || handle.query_channel(port_id, channel_id, height),
            )
        } else {
            handle.query_channel(port_id, channel_id, height)
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.handle().query_channel_client_state(request)
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.handle().proven_client_state(client_id, height)
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.handle().proven_connection(connection_id, height)
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.handle()
            .proven_client_consensus(client_id, consensus_height, height)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.handle()
            .build_header(trusted_height, target_height, client_state)
    }

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        dst_config: ChainConfig,
    ) -> Result<AnyClientState, Error> {
        self.handle().build_client_state(height, dst_config)
    }

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.handle()
            .build_consensus_state(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.handle().check_misbehaviour(update, client_state)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.handle().build_connection_proofs_and_client_state(
            message_type,
            connection_id,
            client_id,
            height,
        )
    }

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.handle()
            .build_channel_proofs(port_id, channel_id, height)
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<(Vec<u8>, Proofs), Error> {
        self.handle()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.handle().query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        self.handle().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.handle().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.handle().query_unreceived_acknowledgement(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.handle().query_txs(request)
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        self.handle().query_blocks(request)
    }
}
