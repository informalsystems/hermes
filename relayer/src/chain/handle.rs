use std::fmt::Debug;
use std::sync::Arc;

use crossbeam_channel as channel;
use dyn_clone::DynClone;
use serde::{Serialize, Serializer};

use ibc::ics02_client::client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::events::UpdateClient;
use ibc::ics02_client::misbehaviour::AnyMisbehaviour;
use ibc::{
    events::IbcEvent,
    ics02_client::header::AnyHeader,
    ics03_connection::{connection::ConnectionEnd, version::Version},
    ics04_channel::{
        channel::ChannelEnd,
        packet::{PacketMsgType, Sequence},
    },
    ics23_commitment::commitment::CommitmentPrefix,
    ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
    proofs::Proofs,
    signer::Signer,
    Height,
};
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_proto::ibc::core::client::v1::QueryConsensusStatesRequest;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
pub use prod::ProdChainHandle;

use crate::connection::ConnectionMsgType;
use crate::keyring::store::KeyEntry;
use crate::{error::Error, event::monitor::EventBatch};
use ibc::query::QueryTxRequest;

mod prod;

pub type Subscription = channel::Receiver<Arc<EventBatch>>;

pub type ReplyTo<T> = channel::Sender<Result<T, Error>>;
pub type Reply<T> = channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

/// Requests that a `ChainHandle` may send to a `ChainRuntime`.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum ChainRequest {
    Terminate {
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

    BuildHeader {
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
        reply_to: ReplyTo<AnyHeader>,
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
        reply_to: ReplyTo<Option<AnyMisbehaviour>>,
    },

    BuildConnectionProofsAndClientState {
        message_type: ConnectionMsgType,
        connection_id: ConnectionId,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(Option<AnyClientState>, Proofs)>,
    },

    QueryClients {
        request: QueryClientStatesRequest,
        reply_to: ReplyTo<Vec<ClientId>>,
    },

    QueryClientState {
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    },

    QueryConsensusStates {
        request: QueryConsensusStatesRequest,
        reply_to: ReplyTo<Vec<AnyConsensusStateWithHeight>>,
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
        reply_to: ReplyTo<ConnectionEnd>,
    },

    QueryChannel {
        port_id: PortId,
        channel_id: ChannelId,
        height: Height,
        reply_to: ReplyTo<ChannelEnd>,
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

// Make `clone` accessible to a ChainHandle object
dyn_clone::clone_trait_object!(ChainHandle);

pub trait ChainHandle: DynClone + Send + Sync + Debug {
    fn id(&self) -> ChainId;

    fn subscribe(&self) -> Result<Subscription, Error>;

    /// Send a transaction with `msgs` to chain.
    fn send_msgs(&self, proto_msgs: Vec<prost_types::Any>) -> Result<Vec<IbcEvent>, Error>;

    fn get_signer(&self) -> Result<Signer, Error>;

    fn get_key(&self) -> Result<KeyEntry, Error>;

    fn module_version(&self, port_id: &PortId) -> Result<String, Error>;

    fn query_latest_height(&self) -> Result<Height, Error>;

    fn query_clients(&self, request: QueryClientStatesRequest) -> Result<Vec<ClientId>, Error>;

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error>;

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error>;

    fn query_upgraded_client_state(
        &self,
        height: Height,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn query_upgraded_consensus_state(
        &self,
        height: Height,
    ) -> Result<(AnyConsensusState, MerkleProof), Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error>;

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error>;

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error>;

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<ChannelEnd, Error>;

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
    ) -> Result<AnyHeader, Error>;

    /// Constructs a client state at the given height
    fn build_client_state(&self, height: Height) -> Result<AnyClientState, Error>;

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
    ) -> Result<Option<AnyMisbehaviour>, Error>;

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
    ) -> Result<(Vec<PacketState>, Height), Error>;

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error>;

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, Height), Error>;

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error>;
}

impl Serialize for dyn ChainHandle {
    fn serialize<S>(&self, serializer: S) -> Result<<S as Serializer>::Ok, <S as Serializer>::Error>
    where
        S: Serializer,
    {
        self.id().serialize(serializer)
    }
}
