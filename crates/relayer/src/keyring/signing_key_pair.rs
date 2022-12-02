use core::any::Any;

use hdpath::StandardHDPath;
use serde::{de::DeserializeOwned, Serialize};

use super::{errors::Error, KeyFile, KeyType};
use crate::config::AddressType;

pub trait SigningKeyPair {
    const KEY_TYPE: KeyType;

    fn from_key_file(key_file: KeyFile, hd_path: &StandardHDPath) -> Result<Self, Error>
    where
        Self: Sized;

    fn from_seed_file(contents: &str, hd_path: &StandardHDPath) -> Result<Self, Error>
    where
        Self: Sized,
    {
        let key_file = serde_json::from_str(contents).map_err(Error::encode)?;
        Self::from_key_file(key_file, hd_path)
    }

    fn from_mnemonic(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: &AddressType,
        account_prefix: &str,
    ) -> Result<Self, Error>
    where
        Self: Sized;

    fn account(&self) -> String;
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error>;

    fn as_any(&self) -> &dyn Any;
}

pub trait SigningKeyPairSized: SigningKeyPair + Clone + DeserializeOwned + Serialize {}

impl<T: SigningKeyPair + Clone + DeserializeOwned + Serialize> SigningKeyPairSized for T {}
