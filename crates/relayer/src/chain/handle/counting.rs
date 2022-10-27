use core::fmt::{Display, Error as FmtError, Formatter};
use std::collections::HashMap;
use std::sync::{Arc, RwLock, RwLockReadGuard};

use crossbeam_channel as channel;
use tracing::{debug, Span};

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::endpoint::{ChainStatus, HealthCheck};
use crate::chain::handle::{ChainHandle, ChainRequest, Subscription};
use crate::chain::requests::*;
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::ChainConfig;
use crate::connection::ConnectionMsgType;
use crate::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use crate::denom::DenomTrace;
use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::keyring::KeyEntry;
use crate::light_client::AnyHeader;
use crate::misbehaviour::MisbehaviourEvidence;
use crate::util::lock::LockExt;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc_relayer_types::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc_relayer_types::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::{
    core::ics03_connection::connection::ConnectionEnd,
    core::ics03_connection::version::Version,
    core::ics04_channel::channel::ChannelEnd,
    core::ics23_commitment::commitment::CommitmentPrefix,
    core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    proofs::Proofs,
    signer::Signer,
    Height,
};

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

impl<Handle: ChainHandle> Display for CountingChainHandle<Handle> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "CountingChainHandle {{ chain_id: {} }}",
            self.inner().id()
        )
    }
}

impl<Handle: ChainHandle> ChainHandle for CountingChainHandle<Handle> {
    fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self {
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
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
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

    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error> {
        self.inc_metric("query_balance");
        self.inner().query_balance(key_name, denom)
    }

    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error> {
        self.inc_metric("query_all_balance");
        self.inner().query_all_balances(key_name)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.inc_metric("query_denom_trace");
        self.inner().query_denom_trace(hash)
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        self.inc_metric("query_application_status");
        self.inner().query_application_status()
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
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        self.inc_metric(&format!(
            "query_client_state({}, {})",
            request.client_id, request.height
        ));
        self.inner().query_client_state(request, include_proof)
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
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.inc_metric("query_consensus_state");
        self.inner().query_consensus_state(request, include_proof)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_client_state");
        self.inner().query_upgraded_client_state(request)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inc_metric("query_upgraded_consensus_state");
        self.inner().query_upgraded_consensus_state(request)
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
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        self.inc_metric("query_connection");
        self.inner().query_connection(request, include_proof)
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
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.inc_metric("query_next_sequence_receive");
        self.inner()
            .query_next_sequence_receive(request, include_proof)
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
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        self.inc_metric("query_channel");
        self.inner().query_channel(request, include_proof)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.inc_metric("query_channel_client_state");
        self.inner().query_channel_client_state(request)
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
        options: ClientSettings,
    ) -> Result<AnyClientState, Error> {
        self.inc_metric("build_client_state");
        self.inner().build_client_state(height, options)
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
    ) -> Result<Proofs, Error> {
        self.inc_metric("build_packet_proofs");
        self.inner()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inc_metric("query_packet_commitment");
        self.inner().query_packet_commitment(request, include_proof)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.inc_metric("query_packet_commitments");
        self.inner().query_packet_commitments(request)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inc_metric("query_packet_receipt");
        self.inner().query_packet_receipt(request, include_proof)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.inc_metric("query_unreceived_packets");
        self.inner().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inc_metric("query_packet_acknowledgement");
        self.inner()
            .query_packet_acknowledgement(request, include_proof)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.inc_metric("query_packet_acknowledgements");
        self.inner().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.inc_metric("query_unreceived_acknowledgement");
        self.inner().query_unreceived_acknowledgements(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.inc_metric("query_txs");
        self.inner().query_txs(request)
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.inc_metric("query_packet_events");
        self.inner().query_packet_events(request)
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        self.inc_metric("query_host_consensus_state");
        self.inner.query_host_consensus_state(request)
    }

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error> {
        self.inc_metric("maybe_register_counterparty_payee");
        self.inner
            .maybe_register_counterparty_payee(channel_id, port_id, counterparty_payee)
    }
}
