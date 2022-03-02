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
    core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
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

use crate::chain::handle::{ChainHandle, ChainRequest, Subscription};
use crate::chain::tx::TrackedMsgs;
use crate::chain::{HealthCheck, StatusResponse};
use crate::config::ChainConfig;
use crate::error::Error;
use crate::util::lock::LockExt;
use crate::{connection::ConnectionMsgType, keyring::KeyEntry};

#[derive(Debug, Clone)]
pub struct CountingChainHandle<Handle> {
    inner: Handle,
    metrics: Arc<RwLock<HashMap<String, u64>>>,
}

impl<Handle> CountingChainHandle<Handle> {
    pub fn new(handle: Handle) -> Self {
        Self {
            inner: handle,
            metrics: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    fn inner(&self) -> &Handle {
        &self.inner
    }

    pub fn metrics(&self) -> RwLockReadGuard<'_, HashMap<String, u64>> {
        self.metrics.acquire_read()
    }

    fn inc_metric(&self, key: &str) {
        let mut metrics = self.metrics.acquire_write();
        if let Some(entry) = metrics.get_mut(key) {
            *entry += 1;
        } else {
            metrics.insert(key.to_string(), 1);
        }
    }
}

impl<Handle: Serialize> Serialize for CountingChainHandle<Handle> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

impl<Handle: ChainHandle> ChainHandle for CountingChainHandle<Handle> {
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self {
        Self::new(Handle::new(chain_id, sender))
    }

    fn id(&self) -> ChainId {
        self.inner().id()
    }

    fn shutdown(&self) -> Result<(), Error> {
        debug!(
            "shutting down chain handle {}. usage metrics for chain: \n {:?}",
            self.id(),
            self.metrics()
        );

        self.inner().shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.inc_metric("health_check");
        self.inner().health_check()
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.inc_metric("subscribe");
        self.inner().subscribe()
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
        self.inc_metric("send_messages_and_wait_commit");
        self.inner().send_messages_and_wait_commit(tracked_msgs)
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.inc_metric("send_messages_and_wait_check_tx");
        self.inner().send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.inc_metric("get_signer");
        self.inner().get_signer()
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.inc_metric("config");
        self.inner().config()
    }

    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.inc_metric("get_key");
        self.inner().get_key()
    }

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error> {
        self.inc_metric("add_key");
        self.inner().add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        self.inc_metric("ibc_version");
        self.inner().ibc_version()
    }

    fn query_status(&self) -> Result<StatusResponse, Error> {
        self.inc_metric("query_status");
        self.inner().query_status()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        self.inc_metric("query_latest_height");
        self.inner().query_latest_height()
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.inc_metric("query_clients");
        self.inner().query_clients(request)
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error> {
        self.inc_metric(&format!("query_client_state({}, {})", client_id, height));
        self.inner().query_client_state(client_id, height)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.inc_metric("query_client_connections");
        self.inner().query_client_connections(request)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.inc_metric("query_consensus_states");
        self.inner().query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
    ) -> Result<AnyConsensusState, Error> {
        self.inc_metric("query_consensus_state");
        self.inner()
            .query_consensus_state(client_id, consensus_height, query_height)
    }

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_client_state");
        self.inner().query_upgraded_client_state(height)
    }

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_consensus_state");
        self.inner().query_upgraded_consensus_state(height)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.inc_metric("query_commitment_prefix");
        self.inner().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.inc_metric("query_compatible_versions");
        self.inner().query_compatible_versions()
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error> {
        self.inc_metric("query_connection");
        self.inner().query_connection(connection_id, height)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.inc_metric("query_connections");
        self.inner().query_connections(request)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inc_metric("query_connection_channels");
        self.inner().query_connection_channels(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error> {
        self.inc_metric("query_next_sequence_receive");
        self.inner().query_next_sequence_receive(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inc_metric("query_channels");
        self.inner().query_channels(request)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error> {
        self.inc_metric("query_channel");
        self.inner().query_channel(port_id, channel_id, height)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.inc_metric("query_channel_client_state");
        self.inner().query_channel_client_state(request)
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inc_metric("proven_client_state");
        self.inner().proven_client_state(client_id, height)
    }

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        self.inc_metric("proven_connection");
        self.inner().proven_connection(connection_id, height)
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inc_metric("proven_client_consensus");
        self.inner()
            .proven_client_consensus(client_id, consensus_height, height)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.inc_metric("build_header");
        self.inner()
            .build_header(trusted_height, target_height, client_state)
    }

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        dst_config: ChainConfig,
    ) -> Result<AnyClientState, Error> {
        self.inc_metric("build_client_state");
        self.inner().build_client_state(height, dst_config)
    }

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.inc_metric("build_consensus_state");
        self.inner()
            .build_consensus_state(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.inc_metric("check_misbehaviour");
        self.inner().check_misbehaviour(update, client_state)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.inc_metric("build_connection_proofs_and_client_state");
        self.inner().build_connection_proofs_and_client_state(
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
        self.inner()
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
        self.inner()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.inc_metric("query_packet_commitments");
        self.inner().query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error> {
        self.inc_metric("query_unreceived_packets");
        self.inner().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error> {
        self.inc_metric("query_packet_acknowledgements");
        self.inner().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error> {
        self.inc_metric("query_unreceived_acknowledgement");
        self.inner().query_unreceived_acknowledgement(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        self.inc_metric("query_txs");
        self.inner().query_txs(request)
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        self.inc_metric("query_blocks");
        self.inner().query_blocks(request)
    }
}
