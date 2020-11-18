use crate::keyring::errors::{Error, Kind};
use bech32::ToBase32;
use bitcoin::hashes::hex::ToHex;
use bitcoin::secp256k1::{All, Message, Secp256k1};
use bitcoin::{
    network::constants::Network,
    util::bip32::{DerivationPath, ExtendedPrivKey, ExtendedPubKey},
    PrivateKey,
};
use bitcoin_wallet::account::MasterAccount;
use bitcoin_wallet::mnemonic::Mnemonic;
use hdpath::StandardHDPath;
use k256::{
    ecdsa::{signature::Signer, signature::Verifier, Signature, SigningKey, VerifyKey},
    EncodedPoint, SecretKey,
};
use serde_json::Value;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use tendermint::account::Id as AccountId;

pub const KEYSTORE_DEFAULT_FOLDER: &str = ".rrly/keys/";
pub const KEYSTORE_TEST_BACKEND: &str = "keyring-test";
pub const KEYSTORE_FILE_EXTENSION: &str = "key";

pub type Address = Vec<u8>;

pub enum KeyRing {
    MemoryKeyStore { store: BTreeMap<String, String> },
    TestKeyStore { store: Box<Path> },
}

pub enum StoreBackend {
    Memory,
    Test,
}

pub trait KeyRingOperations: Sized {
    fn init(backend: StoreBackend, chain_id: &str) -> Result<KeyRing, Error>;
    fn key_from_seed_file(&self, key_file_content: &str) -> Result<KeyEntry, Error>;
    fn key_from_mnemonic(&self, mnemonic_words: &str) -> Result<KeyEntry, Error>;
    fn get(&mut self, key_id: String) -> Result<KeyEntry, Error>;
    fn add(&mut self, key_id: String, key_content: &str, chain_id: &str) -> Result<(), Error>;
    fn sign(&mut self, key_id: String, msg: Vec<u8>) -> Vec<u8>;
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
    fn init(backend: StoreBackend, chain_id: &str) -> Result<KeyRing, Error> {
        match backend {
            StoreBackend::Memory => {
                let store: BTreeMap<String, String> = BTreeMap::new();
                Ok(KeyRing::MemoryKeyStore { store })
            }
            StoreBackend::Test => {
                // Create keys folder if it does not exist
                let keys_folder = get_test_backend_folder(chain_id).map_err(|e| {
                    Kind::KeyStoreOperation
                        .context(format!("failed to create keys folder: {:?}", e))
                })?;

                fs::create_dir_all(keys_folder.clone())
                    .map_err(|e| Kind::KeyStoreOperation.context("error creating keys folder"))?;

                Ok(KeyRing::TestKeyStore {
                    store: Box::<Path>::from(keys_folder),
                })
            }
        }
    }

    /// Get key from seed file
    fn key_from_seed_file(&self, key_file_content: &str) -> Result<KeyEntry, Error> {
        let key_json: Value =
            serde_json::from_str(key_file_content).map_err(|e| Kind::InvalidKey.context(e))?;

        let signer: AccountId;
        let key: KeyEntry;

        let mnemonic: String = "".to_string();
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
            .and_then(|k| k.derive_priv(&Secp256k1::new(), &DerivationPath::from(hd_path)))
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
    fn get(&mut self, key_id: String) -> Result<KeyEntry, Error> {
        match &self {
            KeyRing::MemoryKeyStore { store: s } => {
                if !s.contains_key(&key_id) {
                    Err(Kind::InvalidKey.into())
                } else {
                    let key_content = s.get(&key_id);
                    match key_content {
                        Some(k) => {
                            let key_entry = self.key_from_seed_file(k).map_err(|e| {
                                Kind::KeyStoreOperation.context("failed to get key entry")
                            })?;
                            Ok(key_entry)
                        }
                        None => Err(Kind::InvalidKey.into()),
                    }
                }
            }
            KeyRing::TestKeyStore { store: s } => {
                // Fetch key from test folder and return key entry
                todo!()
            }
        }
    }

    /// Insert an entry in the key store
    fn add(&mut self, key_id: String, key: &str, chain_id: &str) -> Result<(), Error> {
        match self {
            KeyRing::MemoryKeyStore { store: s } => match s.get(&key_id) {
                Some(s) => Err(Kind::ExistingKey
                    .context("key already exists".to_string())
                    .into()),
                None => {
                    s.insert(key_id, key.to_string());
                    Ok(())
                }
            },
            KeyRing::TestKeyStore { store: s } => {
                // Save file to appropriate location in the keys folder
                let keys_folder = get_test_backend_folder(chain_id).map_err(|e| {
                    Kind::KeyStoreOperation
                        .context(format!("failed to create keys folder: {:?}", e))
                })?;

                let mut filename = Path::new(keys_folder.as_os_str()).join(key_id);
                filename.set_extension(KEYSTORE_FILE_EXTENSION);

                let mut file = File::create(filename)
                    .map_err(|e| Kind::KeyStoreOperation.context("error creating the key file"))?;

                file.write_all(&key.as_bytes())
                    .map_err(|e| Kind::KeyStoreOperation.context("error writing the key file"))?;

                Ok(())
            }
        }
    }

    /// Sign a message
    fn sign(&mut self, key_id: String, msg: Vec<u8>) -> Vec<u8> {
        let key = self.get(key_id).unwrap();
        let private_key_bytes = key.private_key.private_key.to_bytes();
        let signing_key = SigningKey::new(private_key_bytes.as_slice()).unwrap();
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

fn get_test_backend_folder(chain_id: &str) -> Result<PathBuf, Error> {
    let home = dirs::home_dir();
    match home {
        Some(h) => {
            let folder = Path::new(h.as_path())
                .join(KEYSTORE_DEFAULT_FOLDER)
                .join(chain_id)
                .join(KEYSTORE_TEST_BACKEND);
            Ok(folder)
        }
        None => Err(Into::<Error>::into(
            Kind::KeyStoreOperation.context("cannot retrieve home folder location"),
        )),
    }
}
