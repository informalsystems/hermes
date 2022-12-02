use core::any::Any;

use bip39::{Language, Mnemonic, Seed};
use bitcoin::{
    network::constants::Network,
    util::bip32::{ChildNumber, DerivationPath, ExtendedPrivKey, ExtendedPubKey},
};
use digest::Digest;
use generic_array::{typenum::U32, GenericArray};
use hdpath::StandardHDPath;
use ripemd::Ripemd160;
use secp256k1::{Message, PublicKey, Secp256k1, SecretKey};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use strum::{EnumIter, IntoEnumIterator};

use super::{
    errors::Error,
    key_utils::{decode_bech32, encode_bech32, keccak256_hash},
    pub_key::EncodedPubKey,
    KeyFile, KeyType, SigningKeyPair,
};
use crate::config::AddressType;

pub fn private_key_from_mnemonic(
    mnemonic_words: &str,
    hd_path: &StandardHDPath,
) -> Result<ExtendedPrivKey, Error> {
    let mnemonic = Mnemonic::from_phrase(mnemonic_words, Language::English)
        .map_err(Error::invalid_mnemonic)?;

    let seed = Seed::new(&mnemonic, "");

    let base_key =
        ExtendedPrivKey::new_master(Network::Bitcoin, seed.as_bytes()).map_err(|err| {
            Error::bip32_key_generation_failed(Secp256k1KeyPair::KEY_TYPE, err.into())
        })?;

    let private_key = base_key
        .derive_priv(
            &Secp256k1::new(),
            &standard_path_to_derivation_path(hd_path),
        )
        .map_err(|err| {
            Error::bip32_key_generation_failed(Secp256k1KeyPair::KEY_TYPE, err.into())
        })?;

    Ok(private_key)
}

fn standard_path_to_derivation_path(path: &StandardHDPath) -> DerivationPath {
    let child_numbers = vec![
        ChildNumber::from_hardened_idx(path.purpose().as_value().as_number())
            .expect("Purpose is not Hardened"),
        ChildNumber::from_hardened_idx(path.coin_type()).expect("Coin Type is not Hardened"),
        ChildNumber::from_hardened_idx(path.account()).expect("Account is not Hardened"),
        ChildNumber::from_normal_idx(path.change()).expect("Change is Hardened"),
        ChildNumber::from_normal_idx(path.index()).expect("Index is Hardened"),
    ];

    DerivationPath::from(child_numbers)
}

#[derive(Clone, Copy, Debug, Deserialize, EnumIter, Eq, PartialEq, Serialize)]
pub enum Secp256k1AddressType {
    Cosmos,
    Ethermint,
}

impl Secp256k1AddressType {
    /// Derive the address type based on how the address was generated from the
    /// public key.
    fn derive(public_key: &PublicKey, address: &[u8]) -> Result<Self, Error> {
        Self::iter()
            .find(|address_type| {
                let derived_address = get_address(public_key, *address_type);
                derived_address == *address
            })
            .ok_or_else(|| {
                Error::address_type_not_found(address.to_vec(), public_key.serialize().to_vec())
            })
    }
}

impl TryFrom<&AddressType> for Secp256k1AddressType {
    type Error = Error;

    fn try_from(address_type: &AddressType) -> Result<Self, Self::Error> {
        match address_type {
            AddressType::Ethermint { pk_type } if pk_type.ends_with(".ethsecp256k1.PubKey") => {
                Ok(Self::Ethermint)
            }
            AddressType::Cosmos | AddressType::Ethermint { pk_type: _ } => Ok(Self::Cosmos),
        }
    }
}

/// Return an address from a Public Key
pub fn get_address(public_key: &PublicKey, address_type: Secp256k1AddressType) -> [u8; 20] {
    match address_type {
        Secp256k1AddressType::Ethermint => {
            let public_key = public_key.serialize_uncompressed();
            // 0x04 is `SECP256K1_TAG_PUBKEY_UNCOMPRESSED`:
            // https://github.com/bitcoin-core/secp256k1/blob/d7ec49a6893751f068275cc8ddf4993ef7f31756/include/secp256k1.h#L196
            debug_assert_eq!(public_key[0], 0x04);

            let hashed_key = keccak256_hash(&public_key[1..]);
            // right-most 20-bytes from the 32-byte keccak hash
            // (see https://kobl.one/blog/create-full-ethereum-keypair-and-address/)
            hashed_key[12..].try_into().unwrap()
        }
        Secp256k1AddressType::Cosmos => {
            Ripemd160::digest(Sha256::digest(public_key.serialize())).into()
        }
    }
}

// Cosmos address: bech32("cosmos", ripemd160(sha256(public_key)))
// - For bech32, data must be in 5-bit chunks, with zeroes padded at the end.
//
// Ethermint address: bech32("evmos", keccak256(public_key)[12:])
// - They also have ETH-compatible addresses using base64 instead of bech32.
//   Hex addresses contain a 0x prefix.
fn encode_address(account_prefix: &str, address: &[u8]) -> Result<String, Error> {
    encode_bech32(account_prefix, address)
}

// /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\
// WARNING: Changing this struct in backward incompatible way
//          will force users to re-import their keys.
//
// This uses `VersionedKeyPair` to allow for backwards-
// compatible deserialization.
// /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\ /!\
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(try_from = "VersionedKeyPair")]
pub struct Secp256k1KeyPair {
    private_key: SecretKey,
    pub public_key: PublicKey,
    address: [u8; 20],
    address_type: Secp256k1AddressType,
    account: String,
}

// The old `KeyEntry` type
#[derive(Debug, Deserialize)]
struct KeyPairV1 {
    public_key: ExtendedPubKey,
    private_key: ExtendedPrivKey,
    account: String,
    address: Vec<u8>,
}

#[derive(Debug, Deserialize)]
struct KeyPairV2 {
    private_key: SecretKey,
    public_key: PublicKey,
    address: [u8; 20],
    address_type: Secp256k1AddressType,
    account: String,
}

// Note: Since this uses Serde's untagged enums, the serialized formats between
// versions must be incompatible with each other.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum VersionedKeyPair {
    V1(KeyPairV1),
    V2(KeyPairV2),
}

impl TryFrom<VersionedKeyPair> for Secp256k1KeyPair {
    type Error = Error;

    fn try_from(versioned_key_pair: VersionedKeyPair) -> Result<Self, Self::Error> {
        match versioned_key_pair {
            VersionedKeyPair::V1(KeyPairV1 {
                public_key,
                private_key,
                account,
                address,
            }) => {
                let address: [u8; 20] = address
                    .try_into()
                    .map_err(|address_bytes| Error::invalid_address_length(address_bytes, 20))?;
                let address_type = Secp256k1AddressType::derive(&public_key.public_key, &address)?;
                Ok(Self {
                    private_key: private_key.private_key,
                    public_key: public_key.public_key,
                    address,
                    address_type,
                    account,
                })
            }
            VersionedKeyPair::V2(KeyPairV2 {
                private_key,
                public_key,
                address,
                address_type,
                account,
            }) => Ok(Self {
                private_key,
                public_key,
                address,
                address_type,
                account,
            }),
        }
    }
}

impl Secp256k1KeyPair {
    fn from_mnemonic_internal(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: Secp256k1AddressType,
        account_prefix: &str,
    ) -> Result<Self, Error> {
        let private_key = private_key_from_mnemonic(mnemonic, hd_path)?;
        let public_key = ExtendedPubKey::from_priv(&Secp256k1::signing_only(), &private_key);
        let address = get_address(&public_key.public_key, address_type);
        let account = encode_address(account_prefix, &address)?;

        Ok(Self {
            private_key: private_key.private_key,
            public_key: public_key.public_key,
            address,
            address_type,
            account,
        })
    }
}

impl SigningKeyPair for Secp256k1KeyPair {
    const KEY_TYPE: KeyType = KeyType::Secp256k1;

    fn from_key_file(key_file: KeyFile, hd_path: &StandardHDPath) -> Result<Self, Error> {
        // Decode the Bech32-encoded address from the key file
        let keyfile_address_bytes = decode_bech32(&key_file.address)?;

        let encoded_key: EncodedPubKey = key_file.pubkey.parse()?;
        let mut keyfile_pubkey_bytes = encoded_key.into_bytes();

        // Decode the private key from the mnemonic
        let private_key = private_key_from_mnemonic(&key_file.mnemonic, hd_path)?;
        let derived_pubkey = ExtendedPubKey::from_priv(&Secp256k1::signing_only(), &private_key);
        let derived_pubkey_bytes = derived_pubkey.public_key.serialize().to_vec();
        assert!(derived_pubkey_bytes.len() <= keyfile_pubkey_bytes.len());

        // FIXME: For some reason that is currently unclear, the public key decoded from
        //        the keyfile contains a few extraneous leading bytes. To compare both
        //        public keys, we therefore strip those leading bytes off and keep the
        //        common parts.
        let keyfile_pubkey_bytes =
            keyfile_pubkey_bytes.split_off(keyfile_pubkey_bytes.len() - derived_pubkey_bytes.len());

        // Ensure that the public key in the key file and the one extracted from the mnemonic match.
        if keyfile_pubkey_bytes != derived_pubkey_bytes {
            return Err(Error::public_key_mismatch(
                keyfile_pubkey_bytes,
                derived_pubkey_bytes,
            ));
        }

        let address: [u8; 20] = keyfile_address_bytes
            .try_into()
            .map_err(|address_bytes| Error::invalid_address_length(address_bytes, 20))?;
        let address_type = Secp256k1AddressType::derive(&derived_pubkey.public_key, &address)?;

        Ok(Self {
            private_key: private_key.private_key,
            public_key: derived_pubkey.public_key,
            address,
            address_type,
            account: key_file.address,
        })
    }

    fn from_mnemonic(
        mnemonic: &str,
        hd_path: &StandardHDPath,
        address_type: &AddressType,
        account_prefix: &str,
    ) -> Result<Self, Error> {
        Self::from_mnemonic_internal(mnemonic, hd_path, address_type.try_into()?, account_prefix)
    }

    fn account(&self) -> String {
        self.account.to_owned()
    }

    // NOTE: Neither Cosmos nor Ethermint keep `v` (recovery code) in the
    // `(r, s, v)` tuple for secp256k1.
    //
    // Cosmos: https://github.com/cosmos/cosmos-sdk/blob/main/crypto/keys/secp256k1/secp256k1_cgo.go
    // Ethermint:
    // - https://github.com/evmos/ethermint/blob/main/crypto/ethsecp256k1/ethsecp256k1.go
    // - informalsystems/hermes#2863.
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, Error> {
        let hashed_message: GenericArray<u8, U32> = match self.address_type {
            Secp256k1AddressType::Ethermint => keccak256_hash(message).into(),
            Secp256k1AddressType::Cosmos => Sha256::digest(message),
        };

        // SAFETY: hashed_message is 32 bytes, as expected in `Message::from_slice`,
        // so `unwrap` is safe.
        let message = Message::from_slice(&hashed_message).unwrap();

        Ok(Secp256k1::signing_only()
            .sign_ecdsa(&message, &self.private_key)
            .serialize_compact()
            .to_vec())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
