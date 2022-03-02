/*!
   Definition for a proxy [`ChainHandle`] implementation for tagged
   chain handles.

   Since we use the chain handle type to distinguish the chain tags, we will
   run into problem if we have the same concrete `ChainHandle` implementations
   for two chains that are not encapsulated behind an `impl ChainHandle`.

   This is the case for creating N-ary chains, because we cannot rely on the
   existential type encapsulation of `impl ChainHandle` to turn the
   [`ProdChainHandle`](ibc_relayer::chain::handle::ProdChainHandle) to turn
   them into unqiue types.

   A workaround for this is to add a unique tag to `ProdChainHandle` itself,
   so that the type `MonoTagged<Tag, ProdChainHandle>` becomes a unique chain
   handle type.

   We implement [`ChainHandle`] for a `MonoTagged<Tag, Handle>`, since if the
   underlying `Handle` type implements [`ChainHandle`], then a tagged handle
   is still a [`ChainHandle`].
*/

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
    core::ics24_host::identifier::ChainId,
    core::ics24_host::identifier::ChannelId,
    core::ics24_host::identifier::{ClientId, ConnectionId, PortId},
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
use std::collections::HashMap;
use std::sync::{Arc, RwLock, RwLockReadGuard};
use tracing::debug;

use crate::cache::Cache;
use crate::chain::handle::{ChainHandle, ChainRequest, Subscription};
use crate::chain::tx::TrackedMsgs;
use crate::chain::{HealthCheck, StatusResponse};
use crate::config::ChainConfig;
use crate::error::Error;
use crate::util::lock::LockExt;
use crate::{connection::ConnectionMsgType, keyring::KeyEntry};

#[derive(Debug, Clone)]
pub struct CachingChainHandle<Handle> {
    handle: Handle,
    metrics: Arc<RwLock<HashMap<String, u64>>>,
    cache: Cache,
}

impl<Handle> CachingChainHandle<Handle> {
    pub fn new(handle: Handle) -> Self {
        Self {
            handle,
            metrics: Arc::new(RwLock::new(HashMap::new())),
            cache: Cache::new(),
        }
    }

    pub fn handle(&self) -> &Handle {
        &self.handle
    }

    pub fn metrics(&self) -> RwLockReadGuard<'_, HashMap<String, u64>> {
        self.metrics.acquire_read()
    }

    pub fn inc_metric(&self, key: &str) {
        let mut metrics = self.metrics.acquire_write();
        if let Some(entry) = metrics.get_mut(key) {
            *entry += 1;
        } else {
            metrics.insert(key.to_string(), 1);
        }
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
        debug!(
            "shutting down chain handle {}. usage metrics for chain: \n {:?}",
            self.id(),
            self.metrics()
        );

        self.handle().shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.inc_metric("health_check");
        self.handle().health_check()
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.inc_metric("subscribe");
        self.handle().subscribe()
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        self.inc_metric("send_messages_and_wait_commit");
        self.handle().send_messages_and_wait_commit(tracked_msgs)
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.inc_metric("send_messages_and_wait_check_tx");
        self.handle().send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.inc_metric("get_signer");
        self.handle().get_signer()
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.inc_metric("config");
        self.handle().config()
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.inc_metric("get_key");
        self.handle().get_key()
    }

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error> {
        self.inc_metric("add_key");
        self.handle().add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.inc_metric("ibc_version");
        self.handle().ibc_version()
    }

    fn query_status(&self) -> Result<StatusResponse, Error> {
        self.inc_metric("query_status");
        self.handle().query_status()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        self.inc_metric("query_latest_height");
        self.handle().query_latest_height()
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.inc_metric("query_clients");
        self.handle().query_clients(request)
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        self.inc_metric(&format!("query_client_state({}, {})", client_id, height));
        self.handle().query_client_state(client_id, height)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.inc_metric("query_client_connections");
        self.handle().query_client_connections(request)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.inc_metric("query_consensus_states");
        self.handle().query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
    ) -> Result<AnyConsensusState, Error> {
        self.inc_metric("query_consensus_state");
        self.handle()
            .query_consensus_state(client_id, consensus_height, query_height)
    }

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_client_state");
        self.handle().query_upgraded_client_state(height)
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_consensus_state");
        self.handle().query_upgraded_consensus_state(height)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.inc_metric("query_commitment_prefix");
        self.handle().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.inc_metric("query_compatible_versions");
        self.handle().query_compatible_versions()
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        let handle = self.handle();
        self.cache
            .get_or_try_insert_connection_with(connection_id, || {
                self.inc_metric("query_connection");
                handle.query_connection(connection_id, height)
            })
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.inc_metric("query_connections");
        self.handle().query_connections(request)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inc_metric("query_connection_channels");
        self.handle().query_connection_channels(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        self.inc_metric("query_next_sequence_receive");
        self.handle().query_next_sequence_receive(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inc_metric("query_channels");
        self.handle().query_channels(request)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        self.inc_metric("query_channel");
        self.handle().query_channel(port_id, channel_id, height)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.inc_metric("query_channel_client_state");
        self.handle().query_channel_client_state(request)
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inc_metric("proven_client_state");
        self.handle().proven_client_state(client_id, height)
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.inc_metric("proven_connection");
        self.handle().proven_connection(connection_id, height)
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inc_metric("proven_client_consensus");
        self.handle()
            .proven_client_consensus(client_id, consensus_height, height)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.inc_metric("build_header");
        self.handle()
            .build_header(trusted_height, target_height, client_state)
    }

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        dst_config: ChainConfig,
    ) -> Result<AnyClientState, Error> {
        self.inc_metric("build_client_state");
        self.handle().build_client_state(height, dst_config)
    }

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.inc_metric("build_consensus_state");
        self.handle()
            .build_consensus_state(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.inc_metric("check_misbehaviour");
        self.handle().check_misbehaviour(update, client_state)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.inc_metric("build_connection_proofs_and_client_state");
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
        self.inc_metric("build_channel_proofs");
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
        self.inc_metric("build_packet_proofs");
        self.handle()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.inc_metric("query_packet_commitments");
        self.handle().query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        self.inc_metric("query_unreceived_packets");
        self.handle().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.inc_metric("query_packet_acknowledgements");
        self.handle().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.inc_metric("query_unreceived_acknowledgement");
        self.handle().query_unreceived_acknowledgement(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.inc_metric("query_txs");
        self.handle().query_txs(request)
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        self.inc_metric("query_blocks");
        self.handle().query_blocks(request)
    }
}
