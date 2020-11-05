use std::time::Duration;
use std::{collections::HashMap, str::FromStr};

use crossbeam_channel as channel;
use thiserror::Error;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics24_host::{identifier::ChainId, Path, IBC_QUERY_PATH};
use ibc::Height;

use tendermint::net;
use tendermint::{abci::Path as ABCIPath, chain};
use tendermint_rpc::HttpClient;

use crate::config::ChainConfig;
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::util::block_on;

use super::{error::ChainError, Chain};

/// Implementation of handle specific for Cosmos SDK chains
pub mod cosmos;

mod prod;
pub use prod::ProdChainHandle;

pub type Subscription = channel::Receiver<(chain::Id, Height, Vec<IBCEvent>)>;

pub type ReplyTo<T> = channel::Sender<Result<T, ChainError>>;
pub type Reply<T> = channel::Receiver<Result<T, ChainError>>;

pub fn reply_channel<T>() -> (ReplyTo<T>, Reply<T>) {
    channel::bounded(1)
}

/// Inputs that a Handle may send to a Runtime.
pub enum HandleInput {
    Terminate(ReplyTo<()>),

    Subscribe(ReplyTo<Subscription>),

    Query {
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<Vec<u8>>,
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
}

pub trait ChainHandle: Send {
    fn id(&self) -> ChainId;

    fn subscribe(&self, chain_id: ChainId) -> Result<Subscription, ChainError>;

    fn query(&self, path: Path, height: Height, prove: bool) -> Result<Vec<u8>, ChainError>;

    // Inclusion proofs
    // It might be good to include an inclusion proof method which abstracts over the light client
    // to prove that a piece of data is stored on the chain

    fn get_header(&self, height: Height) -> Result<AnyHeader, ChainError>;

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, ChainError>;

    /// Submits a transaction.
    fn submit(&self, transaction: EncodedTransaction) -> Result<(), ChainError>;

    fn get_height(&self, client: &ForeignClient) -> Result<Height, ChainError>;

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, ChainError>;

    /// Given a header originating from this chain, constructs a client state.
    fn assemble_client_state(&self, header: &AnyHeader) -> Result<AnyClientState, ChainError>;

    /// Given a header originating from this chain, constructs a consensus state.
    fn assemble_consensus_state(&self, header: &AnyHeader)
        -> Result<AnyConsensusState, ChainError>;
}
