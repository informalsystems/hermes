// TODO: Update error types for Connection!!

use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("connection state unknown")]
    UnknownState,

    #[error("connection exists (was initialized) already")]
    ConnectionExistsAlready,

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

    #[error("invalid proof")]
    InvalidProof,

    #[error("queried for a non-existing connection")]
    ConnectionNotFound,

    #[error("invalid counterparty")]
    InvalidCounterparty,

    #[error("missing counterparty")]
    MissingCounterparty,

    #[error("missing counterparty prefix")]
    MissingCounterpartyPrefix,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
