use crate::config::ChainConfig;
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::util::block_on;

use ibc::ics24_host::{identifier::ChainId, Path, IBC_QUERY_PATH};
use ibc::Height;

use tendermint::abci::Path as ABCIPath;
use tendermint::block::signed_header::SignedHeader;
use tendermint::net;
use tendermint_rpc::HttpClient;

use crossbeam_channel as channel;
use std::str::FromStr;
use std::time::Duration;
use thiserror::Error;

pub(crate) mod cosmos; // Implementation of handle specific for Cosmos SDK chains.

// Simplified:
// Subscriptions should have provide processing semantics such
// that event processing can fail and potentially be retried. For instance if a IBCEvent
// contains a Packet to be sent to a full node, it's possible that the receiving full node
// will fail but that packet still needs to be sent. In this case the subscription iterable
// semantics should ensure that that same packet is retried on a new full node when
// requested.
pub type Subscription = channel::Receiver<(Height, Vec<IBCEvent>)>;

#[derive(Debug, Clone, Error)]
pub enum ChainHandleError {
    #[error("failed")]
    Failed,

    #[error("requested proof for data in the privateStore")]
    NonProvableData,

    #[error("rpc client returned error: {0}")]
    RPC(String),
}

// Inputs that a Handle may send to a Runtime.
pub enum HandleInput {
    Terminate(channel::Sender<()>),
    Subscribe(channel::Sender<Subscription>),
}

pub trait ChainHandle: Send {
    fn subscribe(&self, chain_id: ChainId) -> Result<Subscription, ChainHandleError>;

    // Inclusion proofs
    // It might be good to include an inclusion proof method which abstracts over the light client
    // to prove that a peice of data is stored on the chain

    fn query(&self, path: Path, height: Height, prove: bool) -> Result<Vec<u8>, ChainHandleError>;

    // TODO: Error Handling, get rid of this?
    fn get_header(&self, height: Height) -> SignedHeader;

    fn get_minimal_set(
        &self,
        from: Height,
        to: Height,
    ) -> Result<Vec<SignedHeader>, ChainHandleError>;

    fn submit(&self, transaction: EncodedTransaction) -> Result<(), ChainHandleError>;

    // Mocked:
    // - query the consensus_state of src on dst
    // - query the highest consensus_state
    // - verify if with the light client
    // - return the height
    // + TODO: Can eventually be populated be pre-populated by a event_monitor subscription to the
    // to the full node
    fn get_height(&self, client: &ForeignClient) -> Result<Height, ChainHandleError>;

    fn id(&self) -> ChainId;

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, ChainHandleError>;
}
