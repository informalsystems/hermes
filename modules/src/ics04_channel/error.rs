use anomaly::{BoxError, Context};
use thiserror::Error;

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
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
