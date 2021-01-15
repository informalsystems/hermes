use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fs;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use bech32::ToBase32;
use bitcoin::{
    network::constants::Network,
    util::bip32::{DerivationPath, ExtendedPrivKey, ExtendedPubKey},
};
use bitcoin::secp256k1::Secp256k1;
use bitcoin_wallet::mnemonic::Mnemonic;
use hdpath::StandardHDPath;
use k256::ecdsa::{Signature, signature::Signer, SigningKey};
use serde_json::Value;
use tendermint::account::Id as AccountId;

use crate::config::ChainConfig;
use crate::keyring::errors::{Error, Kind};

pub const KEYSTORE_DEFAULT_FOLDER: &str = ".rrly/keys/";
pub const KEYSTORE_TEST_BACKEND: &str = "keyring-test";
pub const KEYSTORE_FILE_EXTENSION: &str = "json";

pub type Address = Vec<u8>;

pub enum KeyRing {
    MemoryKeyStore {
        store: BTreeMap<String, String>,
        chain_config: ChainConfig,
    },
    TestKeyStore {
        store: Box<Path>,
        chain_config: ChainConfig,
    },
}

pub enum StoreBackend {
    Memory,
    Test,
}

pub trait KeyRingOperations: Sized {
    fn init(backend: StoreBackend, chain_config: ChainConfig) -> Result<KeyRing, Error>;
    fn key_from_seed_file(&self, key_file_content: &str) -> Result<KeyEntry, Error>;
    fn key_from_mnemonic(&self, mnemonic_words: &str) -> Result<KeyEntry, Error>;
    fn get_key(&self) -> Result<KeyEntry, Error>;
    fn add_key(&self, key_contents: &str) -> Result<(), Error>;
    fn sign_msg(&self, msg: Vec<u8>) -> Vec<u8>;
}

/// Key entry stores the Private Key and Public Key as well the address
#[derive(Clone, Debug)]
pub struct KeyEntry {
    /// Public key
    pub public_key: ExtendedPubKey,

    /// Private key
    pub private_key: ExtendedPrivKey,

    /// Address
    pub address: Vec<u8>,

    /// Account Bech32 format - TODO allow hrp
    pub account: String,
}

impl KeyRingOperations for KeyRing {
    /// Initialize a in memory key entry store
    fn init(backend: StoreBackend, chain_config: ChainConfig) -> Result<KeyRing, Error> {
        match backend {
            StoreBackend::Memory => {
                let store: BTreeMap<String, String> = BTreeMap::new();
                Ok(KeyRing::MemoryKeyStore {
                    store,
                    chain_config,
                })
            }
            StoreBackend::Test => {
                // Create keys folder if it does not exist
                let keys_folder = get_test_backend_folder(&chain_config).map_err(|e| {
                    Kind::KeyStoreOperation
                        .context(format!("failed to create keys folder: {:?}", e))
                })?;
                fs::create_dir_all(keys_folder.clone())
                    .map_err(|_| Kind::KeyStoreOperation.context("error creating keys folder"))?;

                Ok(KeyRing::TestKeyStore {
                    store: Box::<Path>::from(keys_folder),
                    chain_config,
                })
            }
        }
    }

    /// Get key from seed file
    fn key_from_seed_file(&self, key_file_content: &str) -> Result<KeyEntry, Error> {
        let key_json: Value =
            serde_json::from_str(key_file_content).map_err(|e| Kind::InvalidKey.context(e))?;

        let _signer: AccountId;
        let key: KeyEntry;

        let _mnemonic: String = "".to_string();
        let mnemonic_value = key_json.get("mnemonic");
        match mnemonic_value {
            Some(m) => {
                let mnemonic = m.as_str();
                match mnemonic {
                    Some(v) => {
                        key = self
                            .key_from_mnemonic(v)
                            .map_err(|e| Kind::InvalidMnemonic.context(e))?;
                        Ok(key)
                    }
                    None => Err(Kind::InvalidMnemonic
                        .context("invalid key file, cannot find mnemonic".to_string())
                        .into()),
                }
            }
            None => Err(Kind::InvalidMnemonic
                .context("invalid key file, cannot find mnemonic".to_string())
                .into()),
        }
    }

    /// Add a key entry in the store using a mnemonic.
    fn key_from_mnemonic(&self, mnemonic_words: &str) -> Result<KeyEntry, Error> {
        // Generate seed from mnemonic
        let mnemonic =
            Mnemonic::from_str(mnemonic_words).map_err(|e| Kind::InvalidMnemonic.context(e))?;
        let seed = mnemonic.to_seed(Some(""));

        // Get Private Key from seed and standard derivation path
        let hd_path = StandardHDPath::try_from("m/44'/118'/0'/0/0").unwrap();
        let private_key = ExtendedPrivKey::new_master(Network::Bitcoin, &seed.0)
            .and_then(|k| {
                k.derive_priv(
                    &Secp256k1::new(),
                    &DerivationPath::from_str(hd_path.to_string().as_str()).unwrap(),
                )
            })
            .map_err(|e| Kind::PrivateKey.context(e))?;

        // Get Public Key from Private Key
        let public_key = ExtendedPubKey::from_private(&Secp256k1::new(), &private_key);

        // Get address from the Public Key
        let address = get_address(public_key);

        // Get Bech32 account
        let account = bech32::encode("cosmos", address.to_base32())
            .map_err(|e| Kind::Bech32Account.context(e))?;

        let key = KeyEntry {
            public_key,
            private_key,
            address,
            account,
        };

        Ok(key)
    }

    /// Return a key entry from a key name
    fn get_key(&self) -> Result<KeyEntry, Error> {
        match &self {
            KeyRing::MemoryKeyStore {
                store,
                chain_config,
            } => {
                if !store.contains_key(chain_config.key_name.clone().as_str()) {
                    Err(Kind::InvalidKey.into())
                } else {
                    let key_content = store.get(chain_config.key_name.as_str());
                    match key_content {
                        Some(k) => {
                            let key_entry = self.key_from_seed_file(k).map_err(|_| {
                                Kind::KeyStoreOperation.context("failed to get key entry")
                            })?;
                            Ok(key_entry)
                        }
                        None => Err(Kind::InvalidKey.into()),
                    }
                }
            }
            KeyRing::TestKeyStore {
                store: _store,
                chain_config,
            } => {
                // Fetch key from test folder and return key entry
                let keys_folder = get_test_backend_folder(chain_config).map_err(|e| {
                    Kind::KeyStoreOperation
                        .context(format!("failed to retrieve keys folder: {:?}", e))
                })?;

                let mut filename =
                    Path::new(keys_folder.as_os_str()).join(chain_config.key_name.clone());
                filename.set_extension(KEYSTORE_FILE_EXTENSION);

                if Path::exists(filename.as_path()) {
                    let mut file = File::open(filename)
                        .map_err(|_| Kind::KeyStoreOperation.context("cannot open key file"))?;
                    let mut file_contents = String::new();
                    file.read_to_string(&mut file_contents)
                        .map_err(|_| Kind::KeyStoreOperation.context("cannot ready key file"))?;
                    let key_entry =
                        self.key_from_seed_file(file_contents.as_str())
                            .map_err(|_| {
                                Kind::KeyStoreOperation.context("error getting key from file")
                            })?;
                    Ok(key_entry)
                } else {
                    Err(Kind::KeyStoreOperation
                        .context("cannot find key file")
                        .into())
                }
            }
        }
    }

    /// Insert an entry in the key store
    fn add_key(&self, key_contents: &str) -> Result<(), Error> {
        match self {
            KeyRing::MemoryKeyStore {
                store,
                chain_config,
            } => match store.get(chain_config.key_name.clone().as_str()) {
                Some(_s) => Err(Kind::ExistingKey
                    .context("key already exists".to_string())
                    .into()),
                None => {
                    store
                        .clone()
                        .insert(chain_config.key_name.to_string(), key_contents.to_string());
                    Ok(())
                }
            },
            KeyRing::TestKeyStore {
                store: _store,
                chain_config,
            } => {
                // Save file to appropriate location in the keys folder
                let keys_folder = get_test_backend_folder(chain_config).map_err(|e| {
                    Kind::KeyStoreOperation
                        .context(format!("failed to retrieve keys folder: {:?}", e))
                })?;

                let mut filename =
                    Path::new(keys_folder.as_os_str()).join(chain_config.key_name.clone());
                filename.set_extension(KEYSTORE_FILE_EXTENSION);

                let mut file = File::create(filename)
                    .map_err(|_| Kind::KeyStoreOperation.context("error creating the key file"))?;

                file.write_all(&key_contents.as_bytes())
                    .map_err(|_| Kind::KeyStoreOperation.context("error writing the key file"))?;

                Ok(())
            }
        }
    }

    /// Sign a message
    fn sign_msg(&self, msg: Vec<u8>) -> Vec<u8> {
        let key = self.get_key().unwrap();
        let private_key_bytes = key.private_key.private_key.to_bytes();
        let signing_key = SigningKey::from_bytes(private_key_bytes.as_slice()).unwrap();
        let signature: Signature = signing_key.sign(&msg);
        signature.as_ref().to_vec()
    }
}

/// Return an address from a Public Key
fn get_address(pk: ExtendedPubKey) -> Vec<u8> {
    use crypto::digest::Digest;
    use crypto::ripemd160::Ripemd160;
    use crypto::sha2::Sha256;

    let mut sha256 = Sha256::new();
    sha256.input(pk.public_key.to_bytes().as_slice());
    let mut bytes = vec![0; sha256.output_bytes()];
    sha256.result(&mut bytes);
    let mut hash = Ripemd160::new();
    hash.input(bytes.as_slice());
    let mut acct = vec![0; hash.output_bytes()];
    hash.result(&mut acct);
    acct.to_vec()
}

fn get_test_backend_folder(chain_config: &ChainConfig) -> Result<PathBuf, Error> {
    let home = dirs_next::home_dir();
    match home {
        Some(h) => {
            let folder = Path::new(h.as_path())
                .join(KEYSTORE_DEFAULT_FOLDER)
                .join(chain_config.id.as_str())
                .join(KEYSTORE_TEST_BACKEND);
            Ok(folder)
        }
        None => Err(Into::<Error>::into(
            Kind::KeyStoreOperation.context("cannot retrieve home folder location"),
        )),
    }
}
