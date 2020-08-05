use super::client_type::ClientType;

use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics24_host::identifier::{ClientId, ConnectionId};
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

    // TODO: It's unclear what this function is expected to achieve. Document this.
    fn verify_client_consensus_state(
        &self,
        root: &CommitmentRoot,
    ) -> Result<bool, Self::ValidationError>;

    // TODO: ValidationError seems wrong here.
    fn verify_connection_state(
        &self,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProof,
        connection_id: &ConnectionId,
        connection_end: &ConnectionEnd,
    ) -> Result<bool, Self::ValidationError>;
}
