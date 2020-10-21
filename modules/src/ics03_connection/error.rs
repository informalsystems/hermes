// TODO: Update error types for Connection!!
use anomaly::{BoxError, Context};
use thiserror::Error;
pub type Error = anomaly::Error<Kind>;

use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("connection state unknown")]
    InvalidState(i32),

    #[error("connection exists (was initialized) already: {0}")]
    ConnectionExistsAlready(ConnectionId),

    #[error("a different connection exists (was initialized) already for the same connection identifier {0}")]
    ConnectionMismatch(ConnectionId),

    #[error("connection end for identifier {0} was never initialized")]
    UninitializedConnection(ConnectionId),

    #[error("consensus height claimed by the client on the other party is too advanced: {0} (host chain current height: {1})")]
    InvalidConsensusHeight(Height, Height),

    #[error("consensus height claimed by the client on the other party falls outside of trusting period: {0} (host chain current height: {1})")]
    StaleConsensusHeight(Height, Height),

    #[error("identifier error")]
    IdentifierError,

    #[error("invalid version")]
    InvalidVersion,

    #[error("invalid address")]
    InvalidAddress,

    #[error("missing consensus proof height")]
    MissingProofHeight,

    #[error("missing consensus proof height")]
    MissingConsensusHeight,

    #[error("invalid connection proof")]
    InvalidProof,

    #[error("invalid signer")]
    InvalidSigner,

    #[error("queried for a non-existing connection")]
    ConnectionNotFound,

    #[error("invalid counterparty")]
    InvalidCounterparty,

    #[error("counterparty chosen connection id {0} is different than the connection id {1}")]
    ConnectionIdMismatch(ConnectionId, ConnectionId),

    #[error("missing counterparty")]
    MissingCounterparty,

    #[error("missing counterparty prefix")]
    MissingCounterpartyPrefix,

    #[error("the client id does not match any client state: {0}")]
    MissingClient(ClientId),

    #[error("client proof must be present")]
    NullClientProof,

    #[error("the client is frozen")]
    FrozenClient,

    #[error("the connection proof verification failed")]
    ConnectionVerificationFailure,

    #[error("the expected consensus state could not be retrieved")]
    MissingClientConsensusState,

    #[error("the local consensus state could not be retrieved")]
    MissingLocalConsensusState,

    #[error("the consensus proof verification failed (height: {0})")]
    ConsensusStateVerificationFailure(Height),

    #[error("the client state proof verification failed")]
    ClientStateVerificationFailure,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
