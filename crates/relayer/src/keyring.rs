pub mod errors;
pub use any_signing_key_pair::AnySigningKeyPair;
pub use ed25519_key_pair::Ed25519KeyPair;
pub use key_type::KeyType;
pub use secp256k1_key_pair::Secp256k1KeyPair;
pub use signing_key_pair::{
    SigningKeyPair,
    SigningKeyPairSized,
};

mod any_signing_key_pair;
mod ed25519_key_pair;
mod key_type;
mod key_utils;
mod pub_key;
mod secp256k1_key_pair;
mod signing_key_pair;

use alloc::collections::btree_map::BTreeMap as HashMap;
use std::{
    ffi::OsStr,
    fs::{
        self,
        File,
    },
    path::PathBuf,
};

use errors::Error;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use serde::{
    Deserialize,
    Serialize,
};

pub const KEYSTORE_DEFAULT_FOLDER: &str = ".hermes/keys/";
pub const KEYSTORE_DISK_BACKEND: &str = "keyring-test";
pub const KEYSTORE_FILE_EXTENSION: &str = "json";

/// JSON key seed file
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KeyFile {
    name: String,
    r#type: String,
    address: String,
    pubkey: String,
    mnemonic: String,
}

pub trait KeyStore<S> {
    fn get_key(&self, key_name: &str) -> Result<S, Error>;
    fn add_key(&mut self, key_name: &str, key_entry: S) -> Result<(), Error>;
    fn remove_key(&mut self, key_name: &str) -> Result<(), Error>;
    fn keys(&self) -> Result<Vec<(String, S)>, Error>;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Memory<S> {
    account_prefix: String,
    keys: HashMap<String, S>,
}

impl<S> Memory<S> {
    pub fn new(account_prefix: String) -> Self {
        Self {
            account_prefix,
            keys: HashMap::new(),
        }
    }
}

impl<S: SigningKeyPairSized> KeyStore<S> for Memory<S> {
    fn get_key(&self, key_name: &str) -> Result<S, Error> {
        self.keys
            .get(key_name)
            .cloned()
            .ok_or_else(Error::key_not_found)
    }

    fn add_key(&mut self, key_name: &str, key_entry: S) -> Result<(), Error> {
        if self.keys.contains_key(key_name) {
            Err(Error::key_already_exist())
        } else {
            self.keys.insert(key_name.to_string(), key_entry);

            Ok(())
        }
    }

    fn remove_key(&mut self, key_name: &str) -> Result<(), Error> {
        self.keys
            .remove(key_name)
            .ok_or_else(Error::key_not_found)?;

        Ok(())
    }

    fn keys(&self) -> Result<Vec<(String, S)>, Error> {
        Ok(self
            .keys
            .iter()
            .map(|(n, k)| (n.to_string(), k.clone()))
            .collect())
    }
}

// TODO: Rename this to something like `Disk`
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Test {
    account_prefix: String,
    store: PathBuf,
}

impl Test {
    pub fn new(account_prefix: String, store: PathBuf) -> Self {
        Self {
            account_prefix,
            store,
        }
    }
}

impl<S: SigningKeyPairSized> KeyStore<S> for Test {
    fn get_key(&self, key_name: &str) -> Result<S, Error> {
        let mut key_file = self.store.join(key_name);
        key_file.set_extension(KEYSTORE_FILE_EXTENSION);

        if !key_file.as_path().exists() {
            return Err(Error::key_file_not_found(format!("{}", key_file.display())));
        }

        let file = File::open(&key_file).map_err(|e| {
            Error::key_file_io(
                key_file.display().to_string(),
                "failed to open file".to_string(),
                e,
            )
        })?;

        let key_entry = serde_json::from_reader(file)
            .map_err(|e| Error::key_file_decode(format!("{}", key_file.display()), e))?;

        Ok(key_entry)
    }

    fn add_key(&mut self, key_name: &str, key_entry: S) -> Result<(), Error> {
        let mut filename = self.store.join(key_name);
        filename.set_extension(KEYSTORE_FILE_EXTENSION);
        let file_path = filename.display().to_string();

        let file = File::create(filename).map_err(|e| {
            Error::key_file_io(file_path.clone(), "failed to create file".to_string(), e)
        })?;

        serde_json::to_writer_pretty(file, &key_entry)
            .map_err(|e| Error::key_file_encode(file_path, e))?;

        Ok(())
    }

    fn remove_key(&mut self, key_name: &str) -> Result<(), Error> {
        let mut filename = self.store.join(key_name);
        filename.set_extension(KEYSTORE_FILE_EXTENSION);

        fs::remove_file(filename.clone())
            .map_err(|e| Error::remove_io_fail(filename.display().to_string(), e))?;

        Ok(())
    }

    fn keys(&self) -> Result<Vec<(String, S)>, Error> {
        let dir = fs::read_dir(&self.store).map_err(|e| {
            Error::key_file_io(
                self.store.display().to_string(),
                "failed to list keys".to_string(),
                e,
            )
        })?;

        let ext = OsStr::new(KEYSTORE_FILE_EXTENSION);

        dir.into_iter()
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.extension() == Some(ext))
            .flat_map(|path| path.file_stem().map(OsStr::to_owned))
            .flat_map(|stem| stem.to_str().map(ToString::to_string))
            .map(|name| self.get_key(&name).map(|key| (name, key)))
            .collect()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Store {
    Memory,
    Test,
}

impl Default for Store {
    fn default() -> Self {
        Self::Test
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum KeyRing<S> {
    Memory(Memory<S>),
    Test(Test),
}

impl<S: SigningKeyPairSized> KeyRing<S> {
    pub fn new(
        store: Store,
        account_prefix: &str,
        chain_id: &ChainId,
        ks_folder: &Option<PathBuf>,
    ) -> Result<Self, Error> {
        match store {
            Store::Memory => Ok(Self::Memory(Memory::new(account_prefix.to_string()))),

            Store::Test => {
                let keys_folder = disk_store_path(chain_id.as_str(), ks_folder)?;

                // Create keys folder if it does not exist
                fs::create_dir_all(&keys_folder).map_err(|e| {
                    Error::key_file_io(
                        keys_folder.display().to_string(),
                        "failed to create keys folder".to_string(),
                        e,
                    )
                })?;

                Ok(Self::Test(Test::new(
                    account_prefix.to_string(),
                    keys_folder,
                )))
            }
        }
    }

    pub fn get_key(&self, key_name: &str) -> Result<S, Error> {
        match self {
            Self::Memory(m) => m.get_key(key_name),
            Self::Test(d) => d.get_key(key_name),
        }
    }

    pub fn add_key(&mut self, key_name: &str, key_entry: S) -> Result<(), Error> {
        match self {
            Self::Memory(m) => m.add_key(key_name, key_entry),
            Self::Test(d) => d.add_key(key_name, key_entry),
        }
    }

    pub fn remove_key(&mut self, key_name: &str) -> Result<(), Error> {
        match self {
            Self::Memory(m) => m.remove_key(key_name),
            Self::Test(d) => <Test as KeyStore<S>>::remove_key(d, key_name),
        }
    }

    pub fn keys(&self) -> Result<Vec<(String, S)>, Error> {
        match self {
            Self::Memory(m) => m.keys(),
            Self::Test(d) => d.keys(),
        }
    }

    pub fn account_prefix(&self) -> &str {
        match self {
            Self::Memory(m) => &m.account_prefix,
            Self::Test(d) => &d.account_prefix,
        }
    }
}

impl KeyRing<Secp256k1KeyPair> {
    pub fn new_secp256k1(
        store: Store,
        account_prefix: &str,
        chain_id: &ChainId,
        ks_folder: &Option<PathBuf>,
    ) -> Result<Self, Error> {
        Self::new(store, account_prefix, chain_id, ks_folder)
    }
}

impl KeyRing<Ed25519KeyPair> {
    pub fn new_ed25519(
        store: Store,
        account_prefix: &str,
        chain_id: &ChainId,
        ks_folder: &Option<PathBuf>,
    ) -> Result<Self, Error> {
        Self::new(store, account_prefix, chain_id, ks_folder)
    }
}

// Why is this not a method on `ChainConfig`?

fn disk_store_path(folder_name: &str, keystore_folder: &Option<PathBuf>) -> Result<PathBuf, Error> {
    let ks_folder = match keystore_folder {
        Some(folder) => folder.to_owned(),
        None => {
            let home = dirs_next::home_dir().ok_or_else(Error::home_location_unavailable)?;
            home.join(KEYSTORE_DEFAULT_FOLDER)
        }
    };

    let folder = ks_folder.join(folder_name).join(KEYSTORE_DISK_BACKEND);

    Ok(folder)
}
