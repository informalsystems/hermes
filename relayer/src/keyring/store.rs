use std::convert::TryFrom;
use std::fs::{self, File};
use std::path::{Path, PathBuf};

use bech32::{ToBase32, Variant};
use bip39::{Language, Mnemonic, Seed};
use bitcoin::{
    network::constants::Network,
    secp256k1::Secp256k1,
    util::bip32::{DerivationPath, ExtendedPrivKey, ExtendedPubKey},
};
use hdpath::StandardHDPath;
use k256::ecdsa::{signature::Signer, Signature, SigningKey};
use ripemd160::Ripemd160;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::config::ChainConfig;
use crate::keyring::errors::{Error, Kind};

pub const KEYSTORE_DEFAULT_FOLDER: &str = ".hermes/keys/";
pub const KEYSTORE_DISK_BACKEND: &str = "keyring-test"; // TODO: Change to "keyring"
pub const KEYSTORE_FILE_EXTENSION: &str = "json";

/// Key entry stores the Private Key and Public Key as well the address
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KeyEntry {
    /// Public key
    pub public_key: ExtendedPubKey,

    /// Private key
    pub private_key: ExtendedPrivKey,

    /// Account Bech32 format - TODO allow hrp
    pub account: String,

    /// Address
    pub address: Vec<u8>,
}

pub trait KeyStore {
    fn get_key(&self) -> Result<KeyEntry, Error>;
    fn add_key(&mut self, key_entry: KeyEntry) -> Result<(), Error>;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Memory {
    account_prefix: String,
    key_entry: Option<KeyEntry>,
}

impl Memory {
    pub fn new(account_prefix: String, key_entry: Option<KeyEntry>) -> Self {
        Self {
            account_prefix,
            key_entry,
        }
    }
}

impl KeyStore for Memory {
    fn get_key(&self) -> Result<KeyEntry, Error> {
        self.key_entry
            .clone()
            .ok_or_else(|| Kind::KeyNotFound.into())
    }

    fn add_key(&mut self, key_entry: KeyEntry) -> Result<(), Error> {
        if self.key_entry.is_some() {
            return Err(Kind::ExistingKey.into());
        }

        self.key_entry = Some(key_entry);

        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Disk {
    key_name: String,
    account_prefix: String,
    store: PathBuf,
}

impl Disk {
    pub fn new(key_name: String, account_prefix: String, store: PathBuf) -> Self {
        Self {
            key_name,
            account_prefix,
            store,
        }
    }
}

impl KeyStore for Disk {
    fn get_key(&self) -> Result<KeyEntry, Error> {
        let mut filename = self.store.join(&self.key_name);
        filename.set_extension(KEYSTORE_FILE_EXTENSION);

        if !filename.as_path().exists() {
            return Err(Kind::KeyStore.context("cannot find key file").into());
        }

        let file =
            File::open(filename).map_err(|_| Kind::KeyStore.context("cannot open key file"))?;

        let key_entry = serde_json::from_reader(file)
            .map_err(|_| Kind::KeyStore.context("cannot ready key file"))?;

        Ok(key_entry)
    }

    fn add_key(&mut self, key_entry: KeyEntry) -> Result<(), Error> {
        let mut filename = self.store.join(&self.key_name);
        filename.set_extension(KEYSTORE_FILE_EXTENSION);

        let file = File::create(filename)
            .map_err(|_| Kind::KeyStore.context("error creating the key file"))?;

        serde_json::to_writer_pretty(file, &key_entry)
            .map_err(|_| Kind::KeyStore.context("error writing the key file"))?;

        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Store {
    Memory,
    Disk,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum KeyRing {
    Memory(Memory),
    Disk(Disk),
}

impl KeyRing {
    pub fn new(store: Store, chain_config: ChainConfig) -> Result<Self, Error> {
        match store {
            Store::Memory => Ok(Self::Memory(Memory::new(chain_config.account_prefix, None))),

            Store::Disk => {
                // Create keys folder if it does not exist
                let keys_folder = disk_store_path(chain_config.id.as_str()).map_err(|e| {
                    Kind::KeyStore.context(format!("failed to create keys folder: {:?}", e))
                })?;

                fs::create_dir_all(keys_folder.clone())
                    .map_err(|_| Kind::KeyStore.context("error creating keys folder"))?;

                Ok(Self::Disk(Disk::new(
                    chain_config.key_name,
                    chain_config.account_prefix,
                    keys_folder,
                )))
            }
        }
    }

    pub fn get_key(&self) -> Result<KeyEntry, Error> {
        match self {
            KeyRing::Memory(m) => m.get_key(),
            KeyRing::Disk(d) => d.get_key(),
        }
    }

    pub fn add_key(&mut self, key_entry: KeyEntry) -> Result<(), Error> {
        match self {
            KeyRing::Memory(m) => m.add_key(key_entry),
            KeyRing::Disk(d) => d.add_key(key_entry),
        }
    }

    /// Get key from seed file
    pub fn key_from_seed_file(&self, key_file_content: &str) -> Result<KeyEntry, Error> {
        #[derive(Serialize, Deserialize)]
        struct KeyFile {
            name: String,
            r#type: String,
            address: String,
            pubkey: String,
            mnemonic: String,
        }

        let key_file: KeyFile =
            serde_json::from_str(key_file_content).map_err(|e| Kind::InvalidKey.context(e))?;

        let mut key = self
            .key_from_mnemonic(&key_file.mnemonic)
            .map_err(|e| Kind::InvalidMnemonic.context(e))?;

        // Use the account in the key file, otherwise the one decoded from
        // the mnemonic will have the configured account prefix which may
        // not match the one in the key file.
        //
        key.account = key_file.address;

        Ok(key)
    }

    /// Add a key entry in the store using a mnemonic.
    pub fn key_from_mnemonic(&self, mnemonic_words: &str) -> Result<KeyEntry, Error> {
        let mnemonic = Mnemonic::from_phrase(mnemonic_words, Language::English)
            .map_err(|e| Kind::InvalidMnemonic.context(e))?;

        let seed = Seed::new(&mnemonic, "");

        // Get Private Key from seed and standard derivation path
        let hd_path = StandardHDPath::try_from("m/44'/118'/0'/0/0").unwrap();
        let private_key = ExtendedPrivKey::new_master(Network::Bitcoin, seed.as_bytes())
            .and_then(|k| k.derive_priv(&Secp256k1::new(), &DerivationPath::from(hd_path)))
            .map_err(|e| Kind::PrivateKey.context(e))?;

        // Get Public Key from Private Key
        let public_key = ExtendedPubKey::from_private(&Secp256k1::new(), &private_key);

        // Get address from the Public Key
        let address = get_address(public_key);

        // Get Bech32 account
        let account = bech32::encode(self.account_prefix(), address.to_base32(), Variant::Bech32)
            .map_err(|e| Kind::Bech32Account.context(e))?;

        let key = KeyEntry {
            public_key,
            private_key,
            address,
            account,
        };

        Ok(key)
    }

    /// Sign a message
    pub fn sign_msg(&self, msg: Vec<u8>) -> Result<Vec<u8>, Error> {
        let key = self.get_key()?;

        let private_key_bytes = key.private_key.private_key.to_bytes();
        let signing_key = SigningKey::from_bytes(private_key_bytes.as_slice()).map_err(|_| {
            Kind::InvalidKey.context("could not build signing key from private key bytes")
        })?;

        let signature: Signature = signing_key.sign(&msg);
        Ok(signature.as_ref().to_vec())
    }

    pub fn account_prefix(&self) -> &str {
        match self {
            KeyRing::Memory(m) => &m.account_prefix,
            KeyRing::Disk(d) => &d.account_prefix,
        }
    }
}

/// Return an address from a Public Key
fn get_address(pk: ExtendedPubKey) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(pk.public_key.to_bytes().as_slice());

    // Read hash digest over the public key bytes & consume hasher
    let pk_hash = hasher.finalize();

    // Plug the hash result into the next crypto hash function.
    let mut rip_hasher = Ripemd160::new();
    rip_hasher.update(pk_hash);
    let rip_result = rip_hasher.finalize();

    rip_result.to_vec()
}

fn disk_store_path(folder_name: &str) -> Result<PathBuf, Error> {
    let home = dirs_next::home_dir()
        .ok_or_else(|| Kind::KeyStore.context("cannot retrieve home folder location"))?;

    let folder = Path::new(home.as_path())
        .join(KEYSTORE_DEFAULT_FOLDER)
        .join(folder_name)
        .join(KEYSTORE_DISK_BACKEND);

    Ok(folder)
}
