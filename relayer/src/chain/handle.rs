use std::sync::Arc;

use crossbeam_channel as channel;

use ibc::{
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics03_connection::connection::ConnectionEnd,
    ics04_channel::channel::ChannelEnd,
    ics24_host::identifier::{ChannelId, ConnectionId, PortId},
    proofs::Proofs,
};
use ibc::{ics23_commitment::commitment::CommitmentPrefix, Height};
use ibc::{
    ics23_commitment::merkle::MerkleProof,
    ics24_host::{identifier::ChainId, identifier::ClientId, Path},
};

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;

use crate::connection::ConnectionMsgType;
use crate::{error::Error, event::monitor::EventBatch};
// use crate::foreign_client::ForeignClient;

use crate::keyring::store::KeyEntry;

use super::QueryResponse;

mod prod;
pub use prod::ProdChainHandle;

pub type Subscription = channel::Receiver<Arc<EventBatch>>;

pub type ReplyTo<T> = channel::Sender<Result<T, Error>>;
pub type Reply<T> = channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

/// Inputs that a Handle may send to a Runtime.
#[derive(Clone, Debug)]
pub enum HandleInput {
    Terminate {
        reply_to: ReplyTo<()>,
    },

    Subscribe {
        reply_to: ReplyTo<Subscription>,
    },

    Query {
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<QueryResponse>,
    },

    SendTx {
        proto_msgs: Vec<prost_types::Any>,
        reply_to: ReplyTo<String>,
    },

    // GetHeader {
    //     height: Height,
    //     reply_to: ReplyTo<AnyHeader>,
    // },
    GetMinimalSet {
        from: Height,
        to: Height,
        reply_to: ReplyTo<Vec<AnyHeader>>,
    },

    // Submit {
    //     transaction: EncodedTransaction,
    //     reply_to: ReplyTo<()>,
    // },
    Signer {
        reply_to: ReplyTo<AccountId>,
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

    // CreatePacket {
    //     event: IBCEvent,
    //     reply_to: ReplyTo<Packet>,
    // },
    BuildHeader {
        trusted_height: Height,
        target_height: Height,
        reply_to: ReplyTo<AnyHeader>,
    },

    BuildClientState {
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    },

    BuildConsensusState {
        height: Height,
        reply_to: ReplyTo<AnyConsensusState>,
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

    QueryCommitmentPrefix {
        reply_to: ReplyTo<CommitmentPrefix>,
    },

    QueryCompatibleVersions {
        reply_to: ReplyTo<Vec<String>>,
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
}

pub trait ChainHandle: Clone + Send + Sync {
    fn id(&self) -> ChainId;

    fn query(&self, path: Path, height: Height, prove: bool) -> Result<QueryResponse, Error>;

    fn subscribe(&self, chain_id: ChainId) -> Result<Subscription, Error>;

    /// Send a transaction with `msgs` to chain.
    fn send_tx(&self, proto_msgs: Vec<prost_types::Any>) -> Result<String, Error>;

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error>;

    fn get_signer(&self) -> Result<AccountId, Error>;

    fn get_key(&self) -> Result<KeyEntry, Error>;

    fn module_version(&self, port_id: &PortId) -> Result<String, Error>;

    fn query_latest_height(&self) -> Result<Height, Error>;

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<AnyClientState, Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<String>, Error>;

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
    ) -> Result<ConnectionEnd, Error>;

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
    ) -> Result<AnyHeader, Error>;

    /// Constructs a client state at the given height
    fn build_client_state(&self, height: Height) -> Result<AnyClientState, Error>;

    /// Constructs a consensus state at the given height
    fn build_consensus_state(&self, height: Height) -> Result<AnyConsensusState, Error>;

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
}
