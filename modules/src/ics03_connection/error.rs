// TODO: Update error types for Connection!!

use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("connection state unknown")]
    UnknownState,

    #[error("identifier error")]
    IdentifierError,

    #[error("invalid version")]
    InvalidVersion,

    #[error("invalid address")]
    InvalidAddress,

    #[error("invalid proof")]
    InvalidProof,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
