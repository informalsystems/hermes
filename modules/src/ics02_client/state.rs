use super::client_type::ClientType;

use crate::ics23_commitment::CommitmentRoot;
use crate::ics24_host::identifier::ClientId;
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

pub trait ClientState {
    type ValidationError: std::error::Error;

    /// Client ID of this state
    fn client_id(&self) -> ClientId;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height of consensus state
    fn get_latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool;

    /// Verifies a proof of the consensus state of the specified client stored on the target machine.
    /// FIXME: Definition is incomplete.
    ///        See https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#required-functions
    fn verify_client_consensus_state(
        &self,
        root: &CommitmentRoot,
    ) -> Result<(), Self::ValidationError>;
}
