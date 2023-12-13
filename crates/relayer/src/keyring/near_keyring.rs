use super::{errors::Error, KeyType, SigningKeyPair};
use crate::config::AddressType;
use core::any::Any;
use hdpath::StandardHDPath;
use near_crypto::InMemorySigner;
use near_crypto::KeyFile;
use near_crypto::Signer;

use serde::{Deserialize, Serialize};
#[derive(Clone, Deserialize, Serialize)]
pub struct NearKeyPair(InMemorySigner);

impl std::fmt::Debug for NearKeyPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NearKeyPair")
            .field("public_key", &self.0.public_key())
            .finish()
    }
}

impl NearKeyPair {
    pub fn inner(&self) -> InMemorySigner {
        self.0.clone()
    }
}

impl SigningKeyPair for NearKeyPair {
    const KEY_TYPE: KeyType = KeyType::Ed25519;
    type KeyFile = KeyFile;

    fn from_key_file(key_file: Self::KeyFile, _hd_path: &StandardHDPath) -> Result<Self, Error> {
        Ok(NearKeyPair(InMemorySigner::from(key_file)))
    }

    fn from_mnemonic(
        _mnemonic: &str,
        _hd_path: &StandardHDPath,
        _address_type: &AddressType,
        _account_prefix: &str,
    ) -> Result<Self, Error> {
        unimplemented!()
    }

    // Near address account_id
    fn account(&self) -> String {
        self.0.account_id.as_str().to_string()
    }

    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(self.0.sign(message).to_string().as_bytes().to_vec())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
