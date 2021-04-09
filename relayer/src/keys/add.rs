use std::{
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

use tokio::runtime::Runtime as TokioRuntime;

use crate::{
    chain::{Chain, CosmosSdkChain},
    config::ChainConfig,
    error::{Error, Kind},
    keyring::store::{KeyEntry, KeyRing},
};

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub config: ChainConfig,
    pub file: PathBuf,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());
    let mut chain = CosmosSdkChain::bootstrap(opts.config, rt)?;

    let key = add_key_file(chain.keybase_mut(), opts.file)?;

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
