use core::any::Any;

use bip39::{
    Language,
    Mnemonic,
    Seed,
};
use ed25519_dalek::{
    SigningKey,
    VerifyingKey,
};
use ed25519_dalek_bip32::{
    ChildIndex,
    DerivationPath,
    ExtendedSigningKey,
};
use hdpath::StandardHDPath;
use serde::{
    Deserialize,
    Serialize,
};
use signature::Signer;

use super::{
    errors::Error,
    KeyFile,
    KeyType,
    SigningKeyPair,
};
use crate::config::AddressType;

pub fn private_key_from_mnemonic(
    mnemonic_words: &str,
    hd_path: &StandardHDPath,
) -> Result<ExtendedSigningKey, Error> {
    let mnemonic = Mnemonic::from_phrase(mnemonic_words, Language::English)
        .map_err(Error::invalid_mnemonic)?;

    let seed = Seed::new(&mnemonic, "");

    let base_key = ExtendedSigningKey::from_seed(seed.as_bytes())
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
    Astria,
}

impl TryFrom<&AddressType> for Ed25519AddressType {
    type Error = Error;

    fn try_from(address_type: &AddressType) -> Result<Self, Self::Error> {
        match address_type {
            AddressType::Cosmos | AddressType::Ethermint { .. } => Err(
                Error::unsupported_address_type(address_type.clone(), Ed25519KeyPair::KEY_TYPE),
            ),
            AddressType::Astria => Ok(Self::Astria),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Ed25519KeyPair {
    signing_key: SigningKey,
    address_type: Ed25519AddressType,
}

impl Ed25519KeyPair {
    fn from_mnemonic_internal(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: Ed25519AddressType,
    ) -> Result<Self, Error> {
        let extended_signing_key = private_key_from_mnemonic(mnemonic, hd_path)?;
        let signing_key = extended_signing_key.signing_key;

        Ok(Self {
            signing_key,
            address_type,
        })
    }

    pub(crate) fn signing_key(&self) -> &SigningKey {
        &self.signing_key
    }
}

impl SigningKeyPair for Ed25519KeyPair {
    const KEY_TYPE: KeyType = KeyType::Ed25519;
    type KeyFile = KeyFile;

    fn from_key_file(key_file: KeyFile, hd_path: &StandardHDPath) -> Result<Self, Error> {
        use ed25519_dalek::PUBLIC_KEY_LENGTH;

        // TODO: Derive this from something in `key_file`
        let address_type = Ed25519AddressType::Astria;
        let key_pair = Self::from_mnemonic_internal(&key_file.mnemonic, hd_path, address_type)?;

        let public_key_vec = &bs58::decode(key_file.pubkey)
            .into_vec()
            .map_err(Error::bs58_decode)?;

        let public_key_bytes: &[u8; PUBLIC_KEY_LENGTH] =
            public_key_vec.as_slice().try_into().map_err(|_| {
                Error::invalid_public_key_length(public_key_vec.len(), PUBLIC_KEY_LENGTH)
            })?;

        let public_key_from_file = match address_type {
            Ed25519AddressType::Solana | Ed25519AddressType::Astria => {
                VerifyingKey::from_bytes(public_key_bytes).map_err(Error::invalid_public_key)?
            }
        };

        if key_pair.signing_key.verifying_key() != public_key_from_file {
            return Err(Error::public_key_mismatch(
                key_pair.signing_key.verifying_key().as_bytes().to_vec(),
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
            Ed25519AddressType::Solana => {
                bs58::encode(&self.signing_key.verifying_key()).into_string()
            }
            Ed25519AddressType::Astria => hex::encode(
                astria_core::sequencer::v1alpha1::Address::from_verification_key(
                    ed25519_consensus::VerificationKey::try_from(
                        self.signing_key.verifying_key().to_bytes(),
                    )
                    .expect("can convert between ed25519 keys"),
                ),
            ),
        }
    }

    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(self.signing_key.sign(message).to_vec())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
