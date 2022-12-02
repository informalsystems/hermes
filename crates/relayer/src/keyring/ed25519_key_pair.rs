use core::any::Any;

use bip39::{Language, Mnemonic, Seed};
use ed25519_dalek::{Keypair, PublicKey, SecretKey};
use ed25519_dalek_bip32::{ChildIndex, DerivationPath, ExtendedSecretKey};
use hdpath::StandardHDPath;
use serde::{Deserialize, Serialize};
use signature::Signer;

use super::{errors::Error, KeyFile, KeyType, SigningKeyPair};
use crate::config::AddressType;

pub fn private_key_from_mnemonic(
    mnemonic_words: &str,
    hd_path: &StandardHDPath,
) -> Result<ExtendedSecretKey, Error> {
    let mnemonic = Mnemonic::from_phrase(mnemonic_words, Language::English)
        .map_err(Error::invalid_mnemonic)?;

    let seed = Seed::new(&mnemonic, "");

    let base_key = ExtendedSecretKey::from_seed(seed.as_bytes())
        .map_err(|err| Error::bip32_key_generation_failed(Ed25519KeyPair::KEY_TYPE, err.into()))?;

    let private_key = base_key
        .derive(&standard_path_to_derivation_path(hd_path))
        .map_err(|err| Error::bip32_key_generation_failed(Ed25519KeyPair::KEY_TYPE, err.into()))?;

    Ok(private_key)
}

fn standard_path_to_derivation_path(path: &StandardHDPath) -> DerivationPath {
    let child_indices = vec![
        ChildIndex::hardened(path.purpose().as_value().as_number())
            .expect("Purpose is not Hardened"),
        ChildIndex::hardened(path.coin_type()).expect("Coin Type is not Hardened"),
        ChildIndex::hardened(path.account()).expect("Account is not Hardened"),
        ChildIndex::normal(path.change()).expect("Change is Hardened"),
        ChildIndex::normal(path.index()).expect("Index is Hardened"),
    ];

    DerivationPath::new(child_indices)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum Ed25519AddressType {
    Solana,
}

impl TryFrom<&AddressType> for Ed25519AddressType {
    type Error = Error;

    fn try_from(address_type: &AddressType) -> Result<Self, Self::Error> {
        match address_type {
            AddressType::Cosmos | AddressType::Ethermint { .. } => Err(
                Error::unsupported_address_type(address_type.clone(), Ed25519KeyPair::KEY_TYPE),
            ),
        }
    }
}

#[derive(Debug, Deserialize, Serialize)]
pub struct Ed25519KeyPair {
    keypair: Keypair,
    address_type: Ed25519AddressType,
}

impl Clone for Ed25519KeyPair {
    fn clone(&self) -> Self {
        let Self {
            keypair: Keypair { secret, public },
            address_type,
        } = self;
        Self {
            keypair: Keypair {
                // Needed as `SecretKey` does not implement `Clone`
                secret: SecretKey::from_bytes(secret.as_bytes()).unwrap(),
                public: *public,
            },
            address_type: *address_type,
        }
    }
}

impl Ed25519KeyPair {
    fn from_mnemonic_internal(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: Ed25519AddressType,
    ) -> Result<Self, Error> {
        let private_key = private_key_from_mnemonic(mnemonic, hd_path)?.secret_key;
        let public_key = (&private_key).into();
        let keypair = Keypair {
            secret: private_key,
            public: public_key,
        };

        Ok(Self {
            keypair,
            address_type,
        })
    }
}

impl SigningKeyPair for Ed25519KeyPair {
    const KEY_TYPE: KeyType = KeyType::Ed25519;

    fn from_key_file(key_file: KeyFile, hd_path: &StandardHDPath) -> Result<Self, Error> {
        // TODO: Derive this from something in `key_file`
        let address_type = Ed25519AddressType::Solana;
        let key_pair = Self::from_mnemonic_internal(&key_file.mnemonic, hd_path, address_type)?;

        let public_key_from_file = match address_type {
            Ed25519AddressType::Solana => PublicKey::from_bytes(
                &bs58::decode(key_file.pubkey)
                    .into_vec()
                    .map_err(Error::bs58_decode)?,
            )
            .map_err(Error::invalid_public_key)?,
        };

        if key_pair.keypair.public != public_key_from_file {
            return Err(Error::public_key_mismatch(
                key_pair.keypair.public.as_bytes().to_vec(),
                public_key_from_file.as_bytes().to_vec(),
            ));
        }
        Ok(key_pair)
    }

    fn from_mnemonic(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: &AddressType,
        _account_prefix: &str,
    ) -> Result<Self, Error> {
        Self::from_mnemonic_internal(mnemonic, hd_path, address_type.try_into()?)
    }

    // Solana address: base58(pubkey)
    fn account(&self) -> String {
        match self.address_type {
            Ed25519AddressType::Solana => bs58::encode(&self.keypair.public).into_string(),
        }
    }

    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(self.keypair.sign(message).as_ref().to_vec())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
