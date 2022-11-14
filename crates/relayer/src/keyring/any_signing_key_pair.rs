use serde::Serialize;

use super::{Ed25519KeyPair, Secp256k1KeyPair, SigningKeyPair};

#[derive(Clone, Debug, Serialize)]
#[serde(untagged)]
pub enum AnySigningKeyPair {
    Secp256k1(Secp256k1KeyPair),
    Ed25519(Ed25519KeyPair),
}

impl AnySigningKeyPair {
    pub fn account(&self) -> String {
        match self {
            Self::Secp256k1(key_pair) => key_pair.account(),
            Self::Ed25519(key_pair) => key_pair.account(),
        }
    }

    pub fn downcast<T: Clone + 'static>(&self) -> Option<T> {
        match self {
            Self::Secp256k1(key_pair) => key_pair.as_any(),
            Self::Ed25519(key_pair) => key_pair.as_any(),
        }
        .downcast_ref::<T>()
        .map(T::clone)
    }
}

impl From<Secp256k1KeyPair> for AnySigningKeyPair {
    fn from(key_pair: Secp256k1KeyPair) -> Self {
        Self::Secp256k1(key_pair)
    }
}

impl From<Ed25519KeyPair> for AnySigningKeyPair {
    fn from(key_pair: Ed25519KeyPair) -> Self {
        Self::Ed25519(key_pair)
    }
}
