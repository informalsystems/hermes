// TODO: Update error types for Connection!!

use crate::ics24_host::identifier::{ClientId, ConnectionId};
use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("connection state unknown")]
    UnknownState,

    #[error("connection exists (was initialized) already: {0}")]
    ConnectionExistsAlready(ConnectionId),

    #[error("a different connection exists (was initialized) already for the same connection identifier")]
    ConnectionMismatch,

    #[error("connection end for this identifier was never initialized")]
    UninitializedConnection,

    #[error("consensus height claimed by the client on the other party is too advanced")]
    InvalidConsensusHeight,

    #[error("consensus height claimed by the client on the other party falls outside of trusting period")]
    StaleConsensusHeight,

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

    #[error("the client state proof verification failed")]
    ClientStateVerificationFailure,

    #[error("the consensus proof verification failed")]
    ConsensusStateVerificationFailure,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
