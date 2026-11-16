use hdpath::StandardHDPath;
use serde::{Deserialize, Serialize};

use super::{errors::Error, MlDsa65KeyPair, Secp256k1KeyPair, SigningKeyPair};
use crate::config::AddressType;

#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CosmosAccountKeyType {
    #[default]
    Secp256k1,
    #[serde(rename = "ml_dsa_65")]
    MlDsa65,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(untagged)]
pub enum CosmosKeyPair {
    // Keep the existing secp256k1 key file format readable.
    Secp256k1(Secp256k1KeyPair),
    MlDsa65(MlDsa65KeyPair),
}

impl CosmosKeyPair {
    pub fn from_seed_file(
        kind: CosmosAccountKeyType,
        contents: &str,
        hd_path: &StandardHDPath,
    ) -> Result<Self, Error> {
        match kind {
            CosmosAccountKeyType::Secp256k1 => {
                Secp256k1KeyPair::from_seed_file(contents, hd_path).map(Self::Secp256k1)
            }
            CosmosAccountKeyType::MlDsa65 => {
                MlDsa65KeyPair::from_seed_file(contents, hd_path).map(Self::MlDsa65)
            }
        }
    }

    pub fn from_mnemonic(
        kind: CosmosAccountKeyType,
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: &AddressType,
        account_prefix: &str,
    ) -> Result<Self, Error> {
        match kind {
            CosmosAccountKeyType::Secp256k1 => {
                Secp256k1KeyPair::from_mnemonic(mnemonic, hd_path, address_type, account_prefix)
                    .map(Self::Secp256k1)
            }
            CosmosAccountKeyType::MlDsa65 => {
                MlDsa65KeyPair::from_mnemonic(mnemonic, hd_path, address_type, account_prefix)
                    .map(Self::MlDsa65)
            }
        }
    }

    pub fn key_type(&self) -> CosmosAccountKeyType {
        match self {
            Self::Secp256k1(_) => CosmosAccountKeyType::Secp256k1,
            Self::MlDsa65(_) => CosmosAccountKeyType::MlDsa65,
        }
    }
}

/// Account operations used by the Cosmos transaction encoder.
pub trait CosmosSigner {
    fn signer_address(&self) -> String;
    fn public_key(&self, address_type: &AddressType) -> (String, Vec<u8>);
    fn sign_tx_bytes(&self, bytes: &[u8]) -> Result<Vec<u8>, Error>;
}

impl CosmosSigner for Secp256k1KeyPair {
    fn signer_address(&self) -> String {
        self.account()
    }

    fn public_key(&self, address_type: &AddressType) -> (String, Vec<u8>) {
        let type_url = match address_type {
            AddressType::Cosmos => "/cosmos.crypto.secp256k1.PubKey".to_string(),
            AddressType::Ethermint { pk_type } => pk_type.clone(),
        };

        (type_url, self.public_key.serialize().to_vec())
    }

    fn sign_tx_bytes(&self, bytes: &[u8]) -> Result<Vec<u8>, Error> {
        self.sign(bytes)
    }
}

impl CosmosSigner for CosmosKeyPair {
    fn signer_address(&self) -> String {
        match self {
            Self::Secp256k1(key) => key.signer_address(),
            Self::MlDsa65(key) => key.account.clone(),
        }
    }

    fn public_key(&self, address_type: &AddressType) -> (String, Vec<u8>) {
        match self {
            Self::Secp256k1(key) => key.public_key(address_type),
            Self::MlDsa65(key) => (MlDsa65KeyPair::TYPE_URL.into(), key.public_key.to_vec()),
        }
    }

    fn sign_tx_bytes(&self, bytes: &[u8]) -> Result<Vec<u8>, Error> {
        match self {
            Self::Secp256k1(key) => key.sign_tx_bytes(bytes),
            Self::MlDsa65(key) => key.sign(bytes),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keyring::AnySigningKeyPair;

    #[test]
    fn cosmos_keys_keep_their_format_and_mldsa_listing_is_public() {
        // BIP39 test vector, for test-only keys.
        let mnemonic = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";
        let hd_path = "m/44'/118'/0'/0/0".parse().unwrap();
        let secp =
            Secp256k1KeyPair::from_mnemonic(mnemonic, &hd_path, &AddressType::Cosmos, "cosmos")
                .unwrap();
        let legacy = serde_json::to_string(&secp).unwrap();
        let restored: CosmosKeyPair = serde_json::from_str(&legacy).unwrap();
        assert_eq!(restored.key_type(), CosmosAccountKeyType::Secp256k1);
        assert_eq!(restored.signer_address(), secp.account());
        assert_eq!(serde_json::to_string(&restored).unwrap(), legacy);
        assert!(AnySigningKeyPair::from(restored)
            .downcast::<Secp256k1KeyPair>()
            .is_some());

        let ml_dsa = CosmosKeyPair::from_mnemonic(
            CosmosAccountKeyType::MlDsa65,
            mnemonic,
            &hd_path,
            &AddressType::Cosmos,
            "dora",
        )
        .unwrap();
        let stored = serde_json::to_string(&ml_dsa).unwrap();
        let restored: CosmosKeyPair = serde_json::from_str(&stored).unwrap();
        let address = ml_dsa.signer_address();
        assert_eq!(restored.signer_address(), address);
        assert_eq!(
            restored.public_key(&AddressType::Cosmos),
            ml_dsa.public_key(&AddressType::Cosmos)
        );
        assert_eq!(
            serde_json::to_value(AnySigningKeyPair::from(restored)).unwrap(),
            serde_json::json!({"account": address, "key_type": "ml_dsa_65"}),
        );
    }
}
