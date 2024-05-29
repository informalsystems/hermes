use core::any::Any;

use namada_sdk::address::Address;
use namada_sdk::key::common::SecretKey;

use crate::config::AddressType;
use crate::keyring::errors::Error;
use crate::keyring::{KeyFile, KeyType, SigningKeyPair};
use hdpath::StandardHDPath;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NamadaKeyPair {
    pub alias: String,
    pub address: Address,
    pub secret_key: SecretKey,
}

impl SigningKeyPair for NamadaKeyPair {
    const KEY_TYPE: KeyType = KeyType::Secp256k1;
    type KeyFile = KeyFile;

    fn from_key_file(_key_file: Self::KeyFile, _hd_path: &StandardHDPath) -> Result<Self, Error> {
        unimplemented!("Namada key can't be restored from a KeyFile")
    }

    fn from_mnemonic(
        _mnemonic: &str,
        _hd_path: &StandardHDPath,
        _address_type: &AddressType,
        _account_prefix: &str,
    ) -> Result<Self, Error> {
        unimplemented!("Namada key can't be restored from a KeyFile")
    }

    fn account(&self) -> String {
        self.address.to_string()
    }

    fn sign(&self, _message: &[u8]) -> Result<Vec<u8>, Error> {
        unimplemented!("don't use this to sign a Namada transaction")
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
