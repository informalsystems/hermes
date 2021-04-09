use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use tokio::runtime::Runtime as TokioRuntime;

use crate::error::{Error, Kind};
use crate::{
    chain::{Chain, CosmosSdkChain},
    keyring::store::KeyRing,
};
use crate::{config::ChainConfig, keyring::store::KeyEntry};
use std::fs;

#[derive(Clone, Debug)]
pub enum KeySource {
    File(PathBuf),
    Mnemonic(String),
}

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub config: ChainConfig,
    pub source: KeySource,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());

    let mut chain = CosmosSdkChain::bootstrap(opts.config, rt)?;

    let key = match opts.source {
        KeySource::File(file) => add_key_file(chain.keybase_mut(), file),
        KeySource::Mnemonic(mnemonic) => add_key_mnemonic(chain.keybase_mut(), &mnemonic),
    }?;

    Ok(format!(
        "Added key '{}' ({}) on chain {}",
        opts.name,
        key.account,
        chain.id()
    ))
}

pub fn add_key_file(keyring: &mut KeyRing, file: impl AsRef<Path>) -> Result<KeyEntry, Error> {
    let key_contents = fs::read_to_string(file)
        .map_err(|_| Kind::KeyBase.context("error reading the key file"))?;

    let key_entry = keyring
        .key_from_seed_file(&key_contents)
        .map_err(|e| Kind::KeyBase.context(e))?;

    keyring
        .add_key(key_entry.clone())
        .map_err(|e| Kind::KeyBase.context(e))?;

    Ok(key_entry)
}

pub fn add_key_mnemonic(keyring: &mut KeyRing, mnemonic: &str) -> Result<KeyEntry, Error> {
    let key_entry = keyring
        .key_from_mnemonic(mnemonic)
        .map_err(|e| Kind::KeyBase.context(e))?;

    keyring
        .add_key(key_entry.clone())
        .map_err(|e| Kind::KeyBase.context(e))?;

    Ok(key_entry)
}
