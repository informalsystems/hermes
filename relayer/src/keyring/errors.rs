use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("cannot retrieve key for address")]
    InvalidKey,

    #[error("invalid mnemonic")]
    InvalidMnemonic,

    #[error("cannot generate private key")]
    PrivateKey,

    #[error("cannot generate bech32 account")]
    Bech32Account,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
