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

    #[error("invalid signer address")]
    InvalidSigner,

    #[error("invalid proof")]
    InvalidProof,

    #[error("invalid proof: missing height")]
    MissingHeight,

    #[error("invalid packet")]
    InvalidPacket,

    #[error("acknowledgement too long")]
    AcknowledgementTooLong,

    #[error("missing counterparty")]
    MissingCounterparty,

    #[error("missing channel end")]
    MissingChannel,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
