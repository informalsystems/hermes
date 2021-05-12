use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("invalid key")]
    InvalidKey,

    #[error("key not found")]
    KeyNotFound,

    #[error("key already exists")]
    ExistingKey,

    #[error("invalid mnemonic")]
    InvalidMnemonic,

    #[error("cannot generate private key")]
    PrivateKey,

    #[error("cannot deserialize the encoded public key")]
    EncodedPublicKey(String),

    #[error("cannot generate bech32 account")]
    Bech32Account,

    #[error("bech32 error")]
    Bech32,

    #[error("mismatch between the public key in the key file and the public key in the mnemonic")]
    PublicKeyMismatch { keyfile: Vec<u8>, mnemonic: Vec<u8> },

    #[error("key store error")]
    KeyStore,

    #[error("invalid HD path: {0}")]
    InvalidHdPath(String),
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
