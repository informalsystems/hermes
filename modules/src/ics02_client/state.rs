use super::client_type::ClientType;

use crate::ics23_commitment::CommitmentRoot;
use crate::Height;

pub trait ConsensusState {
    type ValidationError: std::error::Error;

    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Height of consensus state
    fn height(&self) -> Height;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// Performs basic validation of the consensus state
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}
