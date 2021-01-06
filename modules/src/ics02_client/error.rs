use thiserror::Error;

use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::error::Kind as ICS23Error;
use crate::ics24_host::error::ValidationKind;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Error {
    #[error("unknown client type: {0}")]
    UnknownClientType(String),

    #[error("cannot update client because it was not found: {0}")]
    ClientNotFound(ClientId),

    #[error("consensus state not found at: {0} at height {1}")]
    ConsensusStateNotFound(ClientId, Height),

    #[error("header verification failed")]
    HeaderVerificationFailure,

    #[error("unknown client state type: {0}")]
    UnknownClientStateType(String),

    #[error("unknown client consensus state type: {0}")]
    UnknownConsensusStateType(String),

    #[error("unknown header type: {0}")]
    UnknownHeaderType(String),

    #[error("invalid raw client state, error in decoding: {0}")]
    InvalidRawClientState(String),

    #[error("invalid raw client consensus state, error in decoding: {0}")]
    InvalidRawConsensusState(String),

    #[error("invalid raw header, could not convert because {0}")]
    InvalidRawHeader(String),

    #[error("empty raw header, could not convert")]
    EmptyRawHeader,

    #[error("invalid height result: height cannot end up zero or negative")]
    InvalidHeightResult,

    #[error("invalid address")]
    InvalidAddress,

    #[error("commitment prefix error occurred: {0}")]
    CommitmentPrefixError(ICS23Error),

    #[error("mismatch between client and arguments types, expected: {0:?}")]
    ClientArgsTypeMismatch(ClientType),

    #[error("mismatch raw client consensus state")]
    RawClientAndConsensusStateTypesMismatch {
        state_type: ClientType,
        consensus_type: ClientType,
    },

    #[error("received header is at lower than (or equal) height to client latest height")]
    StaleHeader {
        received_height: Height,
        client_latest_height: Height,
    },

    #[error("identifier parsing/validation error caught: {0}")]
    ValidationError(ValidationKind),

    #[error("generic error caught: {0}")]
    GenericError(String),
}

/// Validation error type, meant for cases when a `parse` error occurs.
impl From<ValidationKind> for Error {
    fn from(v: ValidationKind) -> Self {
        Self::ValidationError(v)
    }
}

/// Catch-all error type, meant for cases when the error is thrown from macros, see e.g.,
/// the use of `attribute!` in `TryFrom<RawObject> for CreateClient`.
impl From<&str> for Error {
    fn from(error_raw: &str) -> Self {
        Self::GenericError(error_raw.to_string())
    }
}

/// Note: Required for cases when there exists a `TryFrom` that returns `Result<_, Error>` but the
/// error case can never occur.
impl From<std::convert::Infallible> for Error {
    fn from(_: std::convert::Infallible) -> Self {
        unreachable!()
    }
}
