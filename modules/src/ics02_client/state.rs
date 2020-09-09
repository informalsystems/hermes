use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::commitment::CommitmentRoot;
use tendermint::block::Height;

#[dyn_clonable::clonable]
pub trait ConsensusState: Clone + std::fmt::Debug {
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Height of consensus state
    fn height(&self) -> Height;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// Performs basic validation of the consensus state
    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>>;
}

#[dyn_clonable::clonable]
pub trait ClientState: Clone + std::fmt::Debug {
    /// Client ID of this state
    fn chain_id(&self) -> String;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height of consensus state
    fn latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool;
}
