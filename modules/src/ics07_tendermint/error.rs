use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics24_host::error::ValidationKind;
use tendermint::{account::Id, validator::Info};

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("invalid trusting period")]
    InvalidTrustingPeriod,

    #[error("invalid unbonding period")]
    InvalidUnboundingPeriod,

    #[error("invalid address")]
    InvalidAddress,

    #[error("invalid header, failed basic validation")]
    InvalidHeader,

    #[error("validation error")]
    ValidationError,

    #[error("invalid raw client state")]
    InvalidRawClientState,

    #[error("invalid chain identifier: raw value {0} with underlying validation error: {1}")]
    InvalidChainId(String, ValidationKind),

    #[error("invalid raw height")]
    InvalidRawHeight,

    #[error("invalid raw client consensus state")]
    InvalidRawConsensusState,

    #[error("invalid raw header")]
    InvalidRawHeader,

    #[error("invalid raw misbehaviour")]
    InvalidRawMisbehaviour,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}

#[derive(Clone, Debug, Error)]
pub enum VerificationError {
    #[error("Couldn't verify signature `{signature:?}` with validator `{validator:?}` on sign_bytes `{sign_bytes:?}`")]
    InvalidSignature {
        /// Signature as a byte array
        signature: Vec<u8>,
        /// Validator which provided the signature
        validator: Box<Info>,
        /// Bytes which were signed
        sign_bytes: Vec<u8>,
    },

    /// Duplicate validator in commit signatures
    #[error("duplicate validator with address {0}")]
    DuplicateValidator(Id),

    /// Insufficient signers overlap
    #[error("insufficient signers overlap {0} {1}")]
    InsufficientOverlap(u64, u64),
}
