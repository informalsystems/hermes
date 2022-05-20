use alloc::sync::Arc;
use core::fmt::{self, Debug};

use crossbeam_channel as channel;
use serde::Serialize;

use ibc::{
    core::{
        ics02_client::{
            client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight},
            client_state::{AnyClientState, IdentifiedAnyClientState},
            events::UpdateClient,
            header::AnyHeader,
            misbehaviour::MisbehaviourEvidence,
        },
        ics03_connection::{
            connection::{ConnectionEnd, IdentifiedConnectionEnd},
            version::Version,
        },
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::{PacketMsgType, Sequence},
        },
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    },
    events::IbcEvent,
    proofs::Proofs,
    query::{QueryBlockRequest, QueryTxRequest},
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    config::ChainConfig,
    connection::ConnectionMsgType,
    error::Error,
    event::monitor::{EventBatch, Result as MonitorResult},
    keyring::KeyEntry,
};

use super::{
    client::ClientSettings,
    requests::{
        QueryChannelClientStateRequest, QueryChannelRequest, QueryChannelsRequest,
        QueryClientConnectionsRequest, QueryClientStateRequest, QueryClientStatesRequest,
        QueryConnectionChannelsRequest, QueryConnectionRequest, QueryConnectionsRequest,
        QueryConsensusStateRequest, QueryConsensusStatesRequest, QueryHostConsensusStateRequest,
        QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
        QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
        QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
    },
    tracking::TrackedMsgs,
};
use super::{ChainStatus, HealthCheck};

mod base;
mod cache;
mod counting;

pub use base::BaseChainHandle;
pub use counting::CountingChainHandle;

pub type CachingChainHandle = cache::CachingChainHandle<BaseChainHandle>;
pub type CountingAndCachingChainHandle =
    cache::CachingChainHandle<CountingChainHandle<BaseChainHandle>>;

/// A pair of [`ChainHandle`]s.
#[derive(Clone)]
pub struct ChainHandlePair<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub a: ChainA,
    pub b: ChainB,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ChainHandlePair<ChainA, ChainB> {
    /// Swap the two handles.
    pub fn swap(self) -> ChainHandlePair<ChainB, ChainA> {
        ChainHandlePair {
            a: self.b,
            b: self.a,
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Debug for ChainHandlePair<ChainA, ChainB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChainHandlePair")
            .field("a", &self.a.id())
            .field("b", &self.b.id())
            .finish()
    }
}

pub type Subscription = channel::Receiver<Arc<MonitorResult<EventBatch>>>;

pub type ReplyTo<T> = channel::Sender<Result<T, Error>>;
pub type Reply<T> = channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

/// Requests that a `ChainHandle` may send to a `ChainRuntime`.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ChainRequest {
    Shutdown {
        reply_to: ReplyTo<()>,
    },

    HealthCheck {
        reply_to: ReplyTo<HealthCheck>,
    },

    Subscribe {
        reply_to: ReplyTo<Subscription>,
    },

    SendMessagesAndWaitCommit {
        tracked_msgs: TrackedMsgs,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    },

    SendMessagesAndWaitCheckTx {
        tracked_msgs: TrackedMsgs,
        reply_to: ReplyTo<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>>,
    },

    Config {
        reply_to: ReplyTo<ChainConfig>,
    },

    Signer {
        reply_to: ReplyTo<Signer>,
    },

    GetKey {
        reply_to: ReplyTo<KeyEntry>,
    },

    AddKey {
        key_name: String,
        key: KeyEntry,
        reply_to: ReplyTo<()>,
    },

    IbcVersion {
        reply_to: ReplyTo<Option<semver::Version>>,
    },

    QueryBalance {
        reply_to: ReplyTo<Balance>,
    },

    QueryApplicationStatus {
        reply_to: ReplyTo<ChainStatus>,
    },

    QueryClients {
        request: QueryClientStatesRequest,
        reply_to: ReplyTo<Vec<IdentifiedAnyClientState>>,
    },

    BuildHeader {
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
        reply_to: ReplyTo<(AnyHeader, Vec<AnyHeader>)>,
    },

    BuildClientState {
        height: Height,
        settings: ClientSettings,
        reply_to: ReplyTo<AnyClientState>,
    },

    BuildConsensusState {
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
        reply_to: ReplyTo<AnyConsensusState>,
    },

    BuildMisbehaviour {
        client_state: AnyClientState,
        update_event: UpdateClient,
        reply_to: ReplyTo<Option<MisbehaviourEvidence>>,
    },

    BuildConnectionProofsAndClientState {
        message_type: ConnectionMsgType,
        connection_id: ConnectionId,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(Option<AnyClientState>, Proofs)>,
    },

    QueryClientState {
        request: QueryClientStateRequest,
        reply_to: ReplyTo<AnyClientState>,
    },

    QueryClientConnections {
        request: QueryClientConnectionsRequest,
        reply_to: ReplyTo<Vec<ConnectionId>>,
    },

    QueryConsensusStates {
        request: QueryConsensusStatesRequest,
        reply_to: ReplyTo<Vec<AnyConsensusStateWithHeight>>,
    },

    QueryConsensusState {
        request: QueryConsensusStateRequest,
        reply_to: ReplyTo<AnyConsensusState>,
    },

    QueryUpgradedClientState {
        request: QueryUpgradedClientStateRequest,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    },

    QueryUpgradedConsensusState {
        request: QueryUpgradedConsensusStateRequest,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    },

    QueryCommitmentPrefix {
        reply_to: ReplyTo<CommitmentPrefix>,
    },

    QueryCompatibleVersions {
        reply_to: ReplyTo<Vec<Version>>,
    },

    QueryConnection {
        request: QueryConnectionRequest,
        reply_to: ReplyTo<ConnectionEnd>,
    },

    QueryConnections {
        request: QueryConnectionsRequest,
        reply_to: ReplyTo<Vec<IdentifiedConnectionEnd>>,
    },

    QueryConnectionChannels {
        request: QueryConnectionChannelsRequest,
        reply_to: ReplyTo<Vec<IdentifiedChannelEnd>>,
    },

    QueryChannels {
        request: QueryChannelsRequest,
        reply_to: ReplyTo<Vec<IdentifiedChannelEnd>>,
    },

    QueryChannel {
        request: QueryChannelRequest,
        reply_to: ReplyTo<ChannelEnd>,
    },

    QueryChannelClientState {
        request: QueryChannelClientStateRequest,
        reply_to: ReplyTo<Option<IdentifiedAnyClientState>>,
    },

    QueryNextSequenceReceive {
        request: QueryNextSequenceReceiveRequest,
        reply_to: ReplyTo<Sequence>,
    },

    ProvenClientState {
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    },

    ProvenConnection {
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<(ConnectionEnd, MerkleProof)>,
    },

    ProvenClientConsensus {
        client_id: ClientId,
        consensus_height: Height,
        height: Height,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    },

    BuildChannelProofs {
        port_id: PortId,
        channel_id: ChannelId,
        height: Height,
        reply_to: ReplyTo<Proofs>,
    },

    BuildPacketProofs {
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: Height,
        reply_to: ReplyTo<(Vec<u8>, Proofs)>,
    },

    QueryPacketCommitments {
        request: QueryPacketCommitmentsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    },

    QueryUnreceivedPackets {
        request: QueryUnreceivedPacketsRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    },

    QueryPacketAcknowledgement {
        request: QueryPacketAcknowledgementsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    },

    QueryUnreceivedAcknowledgement {
        request: QueryUnreceivedAcksRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    },

    QueryPacketEventDataFromTxs {
        request: QueryTxRequest,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    },

    QueryPacketEventDataFromBlocks {
        request: QueryBlockRequest,
        reply_to: ReplyTo<(Vec<IbcEvent>, Vec<IbcEvent>)>,
    },

    QueryHostConsensusState {
        request: QueryHostConsensusStateRequest,
        reply_to: ReplyTo<AnyConsensusState>,
    },
}

pub trait ChainHandle: Clone + Send + Sync + Serialize + Debug + 'static {
    fn new(chain_id: ChainId, sender: channel::Sender<ChainRequest>) -> Self;

    /// Get the [`ChainId`] of this chain.
    fn id(&self) -> ChainId;

    /// Shutdown the chain runtime.
    fn shutdown(&self) -> Result<(), Error>;

    /// Perform a health check
    fn health_check(&self) -> Result<HealthCheck, Error>;

    /// Subscribe to the events emitted by the chain.
    fn subscribe(&self) -> Result<Subscription, Error>;

    /// Send the given `msgs` to the chain, packaged as one or more transactions,
    /// and return the list of events emitted by the chain after the transaction was committed.
    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error>;

    /// Submit messages asynchronously.
    /// Does not block waiting on the chain to produce the
    /// resulting events. Instead of events, this method
    /// returns a set of transaction hashes.
    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error>;

    fn get_signer(&self) -> Result<Signer, Error>;

    fn config(&self) -> Result<ChainConfig, Error>;

    fn get_key(&self) -> Result<KeyEntry, Error>;

    fn add_key(&self, key_name: String, key: KeyEntry) -> Result<(), Error>;

    /// Return the version of the IBC protocol that this chain is running, if known.
    fn ibc_version(&self) -> Result<Option<semver::Version>, Error>;

    /// Query the balance of the current account for the denom used to pay tx fees.
    fn query_balance(&self) -> Result<Balance, Error>;

    fn query_application_status(&self) -> Result<ChainStatus, Error>;

    fn query_latest_height(&self) -> Result<Height, Error> {
        Ok(self.query_application_status()?.height)
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error>;

    fn query_client_state(&self, request: QueryClientStateRequest)
        -> Result<AnyClientState, Error>;

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error>;

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error>;

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error>;

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error>;

    fn query_connection(&self, request: QueryConnectionRequest) -> Result<ConnectionEnd, Error>;

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error>;

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error>;

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    fn query_channel(&self, request: QueryChannelRequest) -> Result<ChannelEnd, Error>;

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error>;

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<(ConnectionEnd, MerkleProof), Error>;

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error>;

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error>;

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<AnyClientState, Error>;

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error>;

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error>;

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error>;

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error>;

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<(Vec<u8>, Proofs), Error>;

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error>;

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error>;

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error>;

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error>;

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error>;

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error>;
}
