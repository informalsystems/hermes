use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("invalid trusting period")]
    InvalidTrustingPeriod,

    #[error("invalid unbounding period")]
    InvalidUnboundingPeriod,

    #[error("invalid address")]
    InvalidAddress,

    #[error("invalid header, failed basic validation")]
    InvalidHeader,

    #[error("validation error")]
    ValidationError,

    #[error("invalid raw client state")]
    InvalidRawClientState,

    #[error("invalid raw height")]
    InvalidRawHeight,

    #[error("invalid raw client consensus state")]
    InvalidRawConsensusState,

    #[error("invalid raw header")]
    InvalidRawHeader,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
