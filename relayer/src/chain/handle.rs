use std::time::Duration;
use std::{collections::HashMap, str::FromStr};

use crossbeam_channel as channel;
use thiserror::Error;

use ibc::{
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics03_connection::connection::ConnectionEnd,
    ics03_connection::msgs::ConnectionMsgType,
    ics24_host::identifier::ConnectionId,
    proofs::Proofs,
};
use ibc::{ics23_commitment::commitment::CommitmentPrefix, Height};
use ibc::{
    ics23_commitment::merkle::MerkleProof,
    ics24_host::{identifier::ChainId, identifier::ClientId, Path, IBC_QUERY_PATH},
};

use tendermint::net;
use tendermint::{abci::Path as ABCIPath, chain};
use tendermint_rpc::HttpClient;

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;

use crate::error::{Error, Kind};
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::util::block_on;
use crate::{config::ChainConfig, keyring::store::KeyEntry};

use super::{Chain, QueryResponse};

mod prod;
pub use prod::ProdChainHandle;

pub type Subscription = channel::Receiver<(chain::Id, Height, Vec<IBCEvent>)>;

pub type ReplyTo<T> = channel::Sender<Result<T, Error>>;
pub type Reply<T> = channel::Receiver<Result<T, Error>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

/// Inputs that a Handle may send to a Runtime.
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

    GetHeader {
        height: Height,
        reply_to: ReplyTo<AnyHeader>,
    },

    GetMinimalSet {
        from: Height,
        to: Height,
        reply_to: ReplyTo<Vec<AnyHeader>>,
    },

    Submit {
        transaction: EncodedTransaction,
        reply_to: ReplyTo<()>,
    },

    KeyAndSigner {
        key_file_contents: String,
        reply_to: ReplyTo<(KeyEntry, AccountId)>,
    },

    QueryLatestHeight {
        reply_to: ReplyTo<Height>,
    },

    CreatePacket {
        event: IBCEvent,
        reply_to: ReplyTo<Packet>,
    },

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

    BuildConnectionProofs {
        message_type: ConnectionMsgType,
        connection_id: ConnectionId,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<Proofs>,
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
}

pub trait ChainHandle: Clone + Send + Sync {
    fn id(&self) -> ChainId;

    fn query(&self, path: Path, height: Height, prove: bool) -> Result<QueryResponse, Error>;

    fn subscribe(&self, chain_id: ChainId) -> Result<Subscription, Error>;

    /// Send a transaction with `msgs` to chain.
    fn send_tx(
        &self,
        proto_msgs: Vec<prost_types::Any>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<String, Error>;

    // Inclusion proofs
    // It might be good to include an inclusion proof method which abstracts over the light client
    // to prove that a piece of data is stored on the chain

    fn get_header(&self, height: Height) -> Result<AnyHeader, Error>;

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error>;

    fn key_and_signer(&self, key_file_contents: String) -> Result<(KeyEntry, AccountId), Error>;

    /// Submits a transaction.
    fn submit(&self, transaction: EncodedTransaction) -> Result<(), Error>;

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, Error>;

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

    fn build_connection_proofs(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Proofs, Error>;
}
