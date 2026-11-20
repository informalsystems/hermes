use std::{fmt, sync::Arc};

use fips204::{
    ml_dsa_65,
    traits::{KeyGen, SerDes, Signer},
};
use hdpath::StandardHDPath;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    errors::Error, key_utils::encode_bech32, pub_key::ProtoAny,
    secp256k1_key_pair::private_key_from_mnemonic, KeyFile, KeyType,
};
use crate::config::AddressType;

#[derive(Clone, Deserialize, Serialize)]
#[serde(try_from = "StoredMlDsa65Key", into = "StoredMlDsa65Key")]
pub struct MlDsa65KeyPair {
    stored: StoredMlDsa65Key,
    pub(super) account: String,
    pub(super) public_key: [u8; ml_dsa_65::PK_LEN],
    private_key: Arc<ml_dsa_65::PrivateKey>,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct StoredMlDsa65Key {
    account_prefix: String,
    mldsa65_seed: [u8; 32],
}

impl fmt::Debug for MlDsa65KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MlDsa65KeyPair")
            .field("account", &self.account)
            .finish_non_exhaustive()
    }
}

impl TryFrom<StoredMlDsa65Key> for MlDsa65KeyPair {
    type Error = Error;

    fn try_from(stored: StoredMlDsa65Key) -> Result<Self, Error> {
        let (public_key, private_key) = ml_dsa_65::KG::keygen_from_seed(&stored.mldsa65_seed);
        let public_key = public_key.into_bytes();
        let address = Sha256::digest(public_key);
        let account = encode_bech32(&stored.account_prefix, &address[..20])?;

        Ok(Self {
            stored,
            account,
            public_key,
            private_key: Arc::new(private_key),
        })
    }
}

impl From<MlDsa65KeyPair> for StoredMlDsa65Key {
    fn from(key: MlDsa65KeyPair) -> Self {
        key.stored
    }
}

impl MlDsa65KeyPair {
    pub(super) const TYPE_URL: &str = "/cosmos.crypto.mldsa65.PubKey";

    pub(super) fn from_mnemonic(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: &AddressType,
        account_prefix: &str,
    ) -> Result<Self, Error> {
        if *address_type != AddressType::Cosmos {
            return Err(Error::unsupported_address_type(
                address_type.clone(),
                KeyType::MlDsa65,
            ));
        }

        // Cosmos SDK v0.55.0 uses the BIP32-derived key bytes as the ML-DSA seed.
        let derived = private_key_from_mnemonic(mnemonic.trim(), hd_path)?;
        StoredMlDsa65Key {
            account_prefix: account_prefix.to_owned(),
            mldsa65_seed: derived.private_key.secret_bytes(),
        }
        .try_into()
    }

    pub(super) fn from_seed_file(contents: &str, hd_path: &StandardHDPath) -> Result<Self, Error> {
        let key_file: KeyFile = serde_json::from_str(contents).map_err(Error::encode)?;
        let public_key: ProtoAny = serde_json::from_str(&key_file.pubkey).map_err(Error::encode)?;
        if public_key.tpe != Self::TYPE_URL {
            return Err(Error::unexpected_account_key_type(public_key.tpe));
        }

        let (prefix, _, _) = bech32::decode(&key_file.address).map_err(Error::bech32_account)?;
        let key = Self::from_mnemonic(&key_file.mnemonic, hd_path, &AddressType::Cosmos, &prefix)?;

        if public_key.key != key.public_key {
            return Err(Error::public_key_mismatch(
                public_key.key,
                key.public_key.to_vec(),
            ));
        }
        if key_file.address != key.account {
            return Err(Error::account_address_mismatch(
                key_file.address,
                key.account,
            ));
        }

        Ok(key)
    }

    pub(super) fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error> {
        self.private_key
            .try_sign(message, &[])
            .map(|signature| signature.to_vec())
            .map_err(|reason| Error::mldsa65_signing_failed(reason.to_owned()))
    }
}
