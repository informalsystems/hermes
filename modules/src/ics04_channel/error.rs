use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics02_client::Error as ICS2Error;
use crate::ics24_host::error::ValidationKind;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("channel state unknown")]
    UnknownState,

    #[error("identifier error")]
    IdentifierError,

    #[error("channel order type unknown")]
    UnknownOrderType,

    #[error("invalid connection hops length")]
    InvalidConnectionHopsLength,

    #[error("invalid version")]
    InvalidVersion,

    #[error("invalid signer address")]
    InvalidSigner,

    #[error("invalid proof")]
    InvalidProof,

    #[error("invalid proof: missing height")]
    MissingHeight,

    #[error("invalid timeout height for the packet")]
    InvalidTimeoutHeight,

    #[error("invalid packet")]
    InvalidPacket,

    #[error("there is no packet in this message")]
    MissingPacket,

    #[error("acknowledgement too long")]
    AcknowledgementTooLong,

    #[error("missing counterparty")]
    MissingCounterparty,

    #[error("missing channel end")]
    MissingChannel,

    #[error("error parsing the timeout height field in the packet: {0}")]
    MalformedHeightInRawPacket(ICS2Error),

    #[error("identifier parsing/validation error caught: {0}")]
    ValidationError(ValidationKind),

    #[error("parsing/validation error for sequence numnbers caught: {0}")]
    SeqNrValidationError(std::num::ParseIntError),

    #[error("generic error caught: {0}")]
    GenericError(String),
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}

/// Validation error type, meant for cases when a `parse` error occurs.
impl From<ValidationKind> for Kind {
    fn from(v: ValidationKind) -> Self {
        Self::ValidationError(v)
    }
}

/// Catch-all error type, meant for cases when the error is thrown from macros, see e.g.,
/// the use of `attribute!` in `TryFrom<RawObject> for OpenInit`.
impl From<&str> for Kind {
    fn from(error_raw: &str) -> Self {
        Self::GenericError(error_raw.to_string())
    }
}

/// Covers conversion from error types that can occur when a `parse` for sequence numbers fails.
impl From<std::num::ParseIntError> for Kind {
    fn from(pe: std::num::ParseIntError) -> Self {
        Self::SeqNrValidationError(pe)
    }
}

/// Note: Required for cases when there exists a `TryFrom` that returns `Result<_, Error>` but the
/// error case can never occur.
impl From<std::convert::Infallible> for Kind {
    fn from(_: std::convert::Infallible) -> Self {
        unreachable!()
    }
}
