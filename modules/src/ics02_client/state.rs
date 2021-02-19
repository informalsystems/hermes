use crate::ics23_commitment::commitment::CommitmentRoot;
use crate::ics24_host::identifier::ChainId;
use crate::Height;

use super::{
    client_def::{AnyClientState, AnyConsensusState},
    client_type::ClientType,
};

#[dyn_clonable::clonable]
pub trait ConsensusState: Clone + std::fmt::Debug + Send + Sync {
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// Performs basic validation of the consensus state
    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>>;

    /// Wrap into an `AnyConsensusState`
    fn wrap_any(self) -> AnyConsensusState;
}

#[dyn_clonable::clonable]
pub trait ClientState: Clone + std::fmt::Debug + Send + Sync {
    /// Return the chain identifier which this client is serving (i.e., the client is verifying
    /// consensus states from this chain).
    fn chain_id(&self) -> ChainId;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height of consensus state
    fn latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool;

    /// Wrap into an `AnyClientState`
    fn wrap_any(self) -> AnyClientState;
}
