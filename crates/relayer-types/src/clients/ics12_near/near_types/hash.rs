use borsh::{to_vec, BorshDeserialize, BorshSerialize};
use core::fmt::{self, Debug, Display};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(
    Deserialize,
    Serialize,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    BorshDeserialize,
    BorshSerialize,
    Hash,
)]
pub struct CryptoHash(pub [u8; 32]);

impl CryptoHash {
    //
    pub const fn new() -> Self {
        Self([0; 32])
    }
    //
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
    /// Calculates hash of given bytes.
    pub fn hash_bytes(bytes: &[u8]) -> CryptoHash {
        CryptoHash(sha2::Sha256::digest(bytes).into())
    }
    /// Calculates hash of borsh-serialised representation of an object.
    ///
    /// Note that if you have a slice of objects to serialise, you might
    /// prefer using [`Self::hash_borsh_slice`] instead.
    pub fn hash_borsh<T: BorshSerialize>(value: &T) -> CryptoHash {
        let mut hasher = Sha256::new();
        hasher.update(&to_vec(&value).expect("never failed"));
        CryptoHash(hasher.finalize().into())
    }
}

impl Default for CryptoHash {
    fn default() -> Self {
        Self::new()
    }
}

impl AsRef<[u8]> for CryptoHash {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl TryFrom<&[u8]> for CryptoHash {
    type Error = String;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != 32 {
            return Err("Wrong size.".to_string());
        }
        let inner: [u8; 32] = bytes
            .try_into()
            .map_err(|_| "convert bytes(&[u8]) to [u8; 32] failed".to_string())?;
        Ok(CryptoHash(inner))
    }
}

impl Debug for CryptoHash {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Debug::fmt(&bs58::encode(self.0).into_string(), f)
    }
}

impl Display for CryptoHash {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&bs58::encode(self.0).into_string(), f)
    }
}

pub fn sha256(data: &[u8]) -> [u8; 32] {
    sha2::Sha256::digest(data).into()
}

pub fn combine_hash(hash1: &CryptoHash, hash2: &CryptoHash) -> CryptoHash {
    CryptoHash(sha256(&[hash1.0.as_ref(), hash2.0.as_ref()].concat()))
}
