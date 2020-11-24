use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("invalid key")]
    InvalidKey,

    #[error("key already exists")]
    ExistingKey,

    #[error("invalid mnemonic")]
    InvalidMnemonic,

    #[error("cannot generate private key")]
    PrivateKey,

    #[error("cannot generate bech32 account")]
    Bech32Account,

    #[error("key store error")]
    KeyStoreOperation,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
