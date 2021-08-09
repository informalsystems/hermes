use std::{
    fmt::{self, Debug},
    sync::Arc,
};

use ibc_proto::ibc::core::connection::v1::QueryConnectionsRequest;
use serde::Serialize;

use ibc::tagged::Tagged;
use ibc::{
    events::IbcEvent,
    ics02_client::{
        client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight},
        client_state::{AnyClientState, IdentifiedAnyClientState},
        events::UpdateClient,
        header::AnyHeader,
        misbehaviour::MisbehaviourEvidence,
    },
    ics03_connection::{connection, version::Version},
    ics04_channel::{
        channel,
        packet::{PacketMsgType, Sequence},
    },
    ics23_commitment::commitment::CommitmentPrefix,
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    proofs::Proofs,
    query::QueryTxRequest,
    signer::Signer,
    Height,
};

use ibc_proto::ibc::core::{
    channel::v1::{
        PacketState, QueryChannelClientStateRequest, QueryChannelsRequest,
        QueryConnectionChannelsRequest, QueryNextSequenceReceiveRequest,
        QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
        QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
    },
    client::v1::{QueryClientStatesRequest, QueryConsensusStatesRequest},
    commitment::v1::MerkleProof,
    connection::v1::QueryClientConnectionsRequest,
};

pub use prod::ProdChainHandle;

use crate::{
    channel::{ChannelEnd, IdentifiedChannelEnd},
    connection::{ConnectionEnd, ConnectionMsgType, IdentifiedConnectionEnd},
    error::Error,
    event::monitor::{EventBatch, Result as MonitorResult},
    keyring::KeyEntry,
};

mod prod;

/// A pair of [`ChainHandle`]s.
#[derive(Clone)]
pub struct ChainHandlePair<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    pub a: ChainA,
    pub b: ChainB,
}

impl<ChainA, ChainB> ChainHandlePair<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    /// Swap the two handles.
    pub fn swap(self) -> ChainHandlePair<ChainB, ChainA> {
        ChainHandlePair {
            a: self.b,
            b: self.a,
        }
    }
}

impl<ChainA, ChainB> Debug for ChainHandlePair<ChainA, ChainB>
where
    ChainA: ChainHandle<ChainB>,
    ChainB: ChainHandle<ChainA>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChainHandlePair")
            .field("a", &self.a.id())
            .field("b", &self.b.id())
            .finish()
    }
}

pub type Subscription = crossbeam_channel::Receiver<Arc<MonitorResult<EventBatch>>>;

pub type ReplyTo<T> = crossbeam_channel::Sender<Result<T, Error>>;
pub type Reply<T> = crossbeam_channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    crossbeam_channel::bounded(1)
}

/// Requests that a `ChainHandle` may send to a `ChainRuntime`.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ChainRequest {
    Shutdown {
        reply_to: ReplyTo<()>,
    },

    Subscribe {
        reply_to: ReplyTo<Subscription>,
    },

    SendMsgs {
        proto_msgs: Vec<prost_types::Any>,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    },

    Signer {
        reply_to: ReplyTo<Signer>,
    },

    Key {
        reply_to: ReplyTo<KeyEntry>,
    },

    ModuleVersion {
        port_id: PortId,
        reply_to: ReplyTo<String>,
    },

    QueryLatestHeight {
        reply_to: ReplyTo<Height>,
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
        client_id: ClientId,
        height: Height,
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
        client_id: ClientId,
        consensus_height: Height,
        query_height: Height,
        reply_to: ReplyTo<AnyConsensusState>,
    },

    QueryUpgradedClientState {
        height: Height,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    },

    QueryUpgradedConsensusState {
        height: Height,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    },

    QueryCommitmentPrefix {
        reply_to: ReplyTo<CommitmentPrefix>,
    },

    QueryCompatibleVersions {
        reply_to: ReplyTo<Vec<Version>>,
    },

    QueryConnection {
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<connection::ConnectionEnd>,
    },

    QueryConnections {
        request: QueryConnectionsRequest,
        reply_to: ReplyTo<Vec<connection::IdentifiedConnectionEnd>>,
    },

    QueryConnectionChannels {
        request: QueryConnectionChannelsRequest,
        reply_to: ReplyTo<Vec<channel::IdentifiedChannelEnd>>,
    },

    QueryChannels {
        request: QueryChannelsRequest,
        reply_to: ReplyTo<Vec<channel::IdentifiedChannelEnd>>,
    },

    QueryChannel {
        port_id: PortId,
        channel_id: ChannelId,
        height: Height,
        reply_to: ReplyTo<channel::ChannelEnd>,
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
        reply_to: ReplyTo<(connection::ConnectionEnd, MerkleProof)>,
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
        reply_to: ReplyTo<(Vec<PacketState>, Height)>,
    },

    QueryUnreceivedPackets {
        request: QueryUnreceivedPacketsRequest,
        reply_to: ReplyTo<Vec<u64>>,
    },

    QueryPacketAcknowledgement {
        request: QueryPacketAcknowledgementsRequest,
        reply_to: ReplyTo<(Vec<PacketState>, Height)>,
    },

    QueryUnreceivedAcknowledgement {
        request: QueryUnreceivedAcksRequest,
        reply_to: ReplyTo<Vec<u64>>,
    },

    QueryPacketEventData {
        request: QueryTxRequest,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    },
}

pub trait ChainHandle<Counterparty = Self>: Clone + Send + Sync + Serialize + Debug {
    fn new(chain_id: ChainId, sender: crossbeam_channel::Sender<ChainRequest>) -> Self;

    /// Get the [`ChainId`] of this chain.
    fn id(&self) -> Tagged<Self, ChainId>;

    /// Shutdown the chain runtime.
    fn shutdown(&self) -> Result<(), Error>;

    /// Subscribe to the events emitted by the chain.
    fn subscribe(&self) -> Result<Subscription, Error>;

    /// Send the given `msgs` to the chain, packaged as one or more transactions,
    /// and return the list of events emitted by the chain after the transaction was committed.
    fn send_msgs(
        &self,
        proto_msgs: Vec<Tagged<Self, prost_types::Any>>,
    ) -> Result<Vec<Tagged<Self, IbcEvent>>, Error>;

    fn get_signer(&self) -> Result<Signer, Error>;

    fn get_key(&self) -> Result<KeyEntry, Error>;

    fn module_version(&self, port_id: Tagged<Self, PortId>) -> Result<String, Error>;

    fn query_latest_height(&self) -> Result<Tagged<Self, Height>, Error>;

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<Tagged<Self, IdentifiedAnyClientState>>, Error>;

    fn query_client_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, AnyClientState>, Error>;

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<Tagged<Self, ConnectionId>>, Error>;

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error>;

    fn query_consensus_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        consensus_height: Tagged<Self, Height>,
        query_height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, AnyConsensusState>, Error>;

    fn query_upgraded_client_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyClientState>, Tagged<Self, MerkleProof>), Error>;

    fn query_upgraded_consensus_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyConsensusState>, Tagged<Self, MerkleProof>), Error>;

    fn query_commitment_prefix(&self) -> Result<Tagged<Self, CommitmentPrefix>, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<Tagged<Self, Version>>, Error>;

    fn query_connection(
        &self,
        connection_id: Tagged<Self, ConnectionId>,
        height: Tagged<Self, Height>,
    ) -> Result<ConnectionEnd<Self, Counterparty>, Error>;

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd<Self, Counterparty>>, Error>;

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd<Self, Counterparty>>, Error>;

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Tagged<Self, Sequence>, Error>;

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd<Self, Counterparty>>, Error>;

    fn query_channel(
        &self,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        height: Tagged<Self, Height>,
    ) -> Result<ChannelEnd<Self, Counterparty>, Error>;

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<Tagged<Self, IdentifiedAnyClientState>>, Error>;

    fn proven_client_state(
        &self,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyClientState>, MerkleProof), Error>;

    fn proven_connection(
        &self,
        connection_id: Tagged<Self, ConnectionId>,
        height: Tagged<Self, Height>,
    ) -> Result<(ConnectionEnd<Self, Counterparty>, MerkleProof), Error>;

    fn proven_client_consensus(
        &self,
        client_id: Tagged<Self, ClientId>,
        consensus_height: Tagged<Self, Height>,
        height: Tagged<Self, Height>,
    ) -> Result<(Tagged<Self, AnyConsensusState>, MerkleProof), Error>;

    fn build_header(
        &self,
        trusted_height: Tagged<Self, Height>,
        target_height: Tagged<Self, Height>,
        client_state: Tagged<Self, AnyClientState>,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error>;

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, AnyClientState>, Error>;

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Tagged<Self, Height>,
        target: Tagged<Self, Height>,
        client_state: Tagged<Self, AnyClientState>,
    ) -> Result<Tagged<Self, AnyConsensusState>, Error>;

    fn check_misbehaviour(
        &self,
        update: Tagged<Self, UpdateClient>,
        client_state: Tagged<Self, AnyClientState>,
    ) -> Result<Option<MisbehaviourEvidence>, Error>;

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: Tagged<Self, ConnectionId>,
        client_id: Tagged<Self, ClientId>,
        height: Tagged<Self, Height>,
    ) -> Result<(Option<Tagged<Self, AnyClientState>>, Tagged<Self, Proofs>), Error>;

    fn build_channel_proofs(
        &self,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        height: Tagged<Self, Height>,
    ) -> Result<Tagged<Self, Proofs>, Error>;

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: Tagged<Self, PortId>,
        channel_id: Tagged<Self, ChannelId>,
        sequence: Tagged<Self, Sequence>,
        height: Tagged<Self, Height>,
    ) -> Result<(Vec<u8>, Proofs), Error>;

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, Tagged<Self, Height>), Error>;

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error>;

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Tagged<Self, Height>), Error>;

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error>;
}
