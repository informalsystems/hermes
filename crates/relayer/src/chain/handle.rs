use alloc::sync::Arc;
use core::fmt::{self, Debug, Display};

use crossbeam_channel as channel;
use tracing::Span;

use ibc_proto::ibc::apps::fee::v1::{
    QueryIncentivizedPacketRequest, QueryIncentivizedPacketResponse,
};
use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    core::{
        ics02_client::events::UpdateClient,
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
    proofs::Proofs,
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::ChainConfig,
    connection::ConnectionMsgType,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::{
        monitor::{EventBatch, Result as MonitorResult},
        IbcEventWithHeight,
    },
    keyring::AnySigningKeyPair,
    light_client::AnyHeader,
    misbehaviour::MisbehaviourEvidence,
};

use super::{
    client::ClientSettings,
    endpoint::{ChainStatus, HealthCheck},
    requests::*,
    tracking::TrackedMsgs,
};

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
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
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
        reply_to: ReplyTo<AnySigningKeyPair>,
    },

    AddKey {
        key_name: String,
        key: AnySigningKeyPair,
        reply_to: ReplyTo<()>,
    },

    IbcVersion {
        reply_to: ReplyTo<Option<semver::Version>>,
    },

    QueryBalance {
        key_name: Option<String>,
        denom: Option<String>,
        reply_to: ReplyTo<Balance>,
    },

    QueryAllBalances {
        key_name: Option<String>,
        reply_to: ReplyTo<Vec<Balance>>,
    },

    QueryDenomTrace {
        hash: String,
        reply_to: ReplyTo<DenomTrace>,
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
        include_proof: IncludeProof,
        reply_to: ReplyTo<(AnyClientState, Option<MerkleProof>)>,
    },

    QueryClientConnections {
        request: QueryClientConnectionsRequest,
        reply_to: ReplyTo<Vec<ConnectionId>>,
    },

    QueryConsensusState {
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(AnyConsensusState, Option<MerkleProof>)>,
    },

    QueryConsensusStateHeights {
        request: QueryConsensusStateHeightsRequest,
        reply_to: ReplyTo<Vec<Height>>,
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
        include_proof: IncludeProof,
        reply_to: ReplyTo<(ConnectionEnd, Option<MerkleProof>)>,
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
        include_proof: IncludeProof,
        reply_to: ReplyTo<(ChannelEnd, Option<MerkleProof>)>,
    },

    QueryChannelClientState {
        request: QueryChannelClientStateRequest,
        reply_to: ReplyTo<Option<IdentifiedAnyClientState>>,
    },

    QueryNextSequenceReceive {
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Sequence, Option<MerkleProof>)>,
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
        reply_to: ReplyTo<Proofs>,
    },

    QueryPacketCommitment {
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    },

    QueryPacketCommitments {
        request: QueryPacketCommitmentsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    },

    QueryPacketReceipt {
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    },

    QueryUnreceivedPackets {
        request: QueryUnreceivedPacketsRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    },

    QueryPacketAcknowledgement {
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    },

    QueryPacketAcknowledgements {
        request: QueryPacketAcknowledgementsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    },

    QueryUnreceivedAcknowledgement {
        request: QueryUnreceivedAcksRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    },

    QueryPacketEventDataFromTxs {
        request: QueryTxRequest,
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
    },

    QueryPacketEventData {
        request: QueryPacketEventDataRequest,
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
    },

    QueryHostConsensusState {
        request: QueryHostConsensusStateRequest,
        reply_to: ReplyTo<AnyConsensusState>,
    },

    MaybeRegisterCounterpartyPayee {
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
        reply_to: ReplyTo<()>,
    },

    CrossChainQuery {
        request: Vec<CrossChainQueryRequest>,
        reply_to: ReplyTo<Vec<CrossChainQueryResponse>>,
    },

    QueryIncentivizedPacket {
        request: QueryIncentivizedPacketRequest,
        reply_to: ReplyTo<QueryIncentivizedPacketResponse>,
    },
}

pub trait ChainHandle: Clone + Display + Send + Sync + Debug + 'static {
    fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self;

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
    ) -> Result<Vec<IbcEventWithHeight>, Error>;

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

    fn get_key(&self) -> Result<AnySigningKeyPair, Error>;

    fn add_key(&self, key_name: String, key: AnySigningKeyPair) -> Result<(), Error>;

    /// Return the version of the IBC protocol that this chain is running, if known.
    fn ibc_version(&self) -> Result<Option<semver::Version>, Error>;

    /// Query the balance of the given account for the given denom.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    /// If no denom is given, behavior must be specified, e.g. using the denom used to pay tx fees
    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error>;

    /// Query the balances from all denom of the given account.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error>;

    /// Query the denomination trace given a trace hash.
    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error>;

    /// Query the latest height and timestamp the application is at
    fn query_application_status(&self) -> Result<ChainStatus, Error>;

    fn query_latest_height(&self) -> Result<Height, Error> {
        Ok(self.query_application_status()?.height)
    }

    /// Performs a query to retrieve the state of all clients that a chain hosts.
    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error>;

    /// Performs a query to retrieve the state of the specified light client. A
    /// proof can optionally be returned along with the result.
    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error>;

    /// Query the consensus state at the specified height for a given client.
    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error>;

    /// Query the heights of every consensus state for a given client.
    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<Height>, Error>;

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

    /// Performs a query to retrieve the connection associated with a given
    /// connection identifier. A proof can optionally be returned along with the
    /// result.
    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error>;

    /// Performs a query to retrieve all channels associated with a connection.
    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    /// Performs a query to retrieve `nextSequenceRecv` stored at path
    /// `path::SeqRecvsPath` as defined in ICS-4. A proof can optionally be
    /// returned along with the result.
    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the channels of a chain.
    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    /// Performs a query to retrieve the channel associated with a given channel
    /// identifier. A proof can optionally be returned along with the result.
    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve the client state for the channel associated
    /// with a given channel identifier.
    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error>;

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
    ) -> Result<Proofs, Error>;

    /// Performs a query to retrieve a stored packet commitment hash, stored on
    /// the chain at path `path::CommitmentsPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the packet commitments hashes
    /// associated with a channel. Returns the corresponding packet sequence
    /// numbers and the height at which they were retrieved.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error>;

    /// Performs a query to retrieve a given packet receipt, stored on the chain at path
    /// `path::CommitmentsPath`. A proof can optionally be returned along with the result.
    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query about which IBC packets in the specified list has not
    /// been received. Returns the sequence numbers of the packets that were not
    /// received.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were received,
    /// while packets 7, 8 were not.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error>;

    /// Performs a query to retrieve a stored packet acknowledgement hash,
    /// stored on the chain at path `path::AcksPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the packet acknowledgements associated
    /// with a channel. Returns the corresponding packet sequence numbers and
    /// the height at which they were retrieved.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error>;

    /// Performs a query about which IBC packets in the specified list has not
    /// been acknowledged. Returns the sequence numbers of the packets that were not
    /// acknowledged.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were acknowledged,
    /// while packets 7, 8 were not.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error>;

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error>;

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error>;

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error>;

    fn cross_chain_query(
        &self,
        request: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error>;

    fn query_incentivized_packet(
        &self,
        request: QueryIncentivizedPacketRequest,
    ) -> Result<QueryIncentivizedPacketResponse, Error>;
}
