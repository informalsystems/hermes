use std::sync::Arc;

use tokio::runtime::Runtime as TokioRuntime;

use crate::{
    chain::{Chain, CosmosSdkChain},
    config::ChainConfig,
    error::{Error, Kind},
    keyring::store::{KeyEntry, KeyRing},
};

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub name: String,
    pub mnemonic: String,
    pub config: ChainConfig,
}

pub fn restore_key(opts: KeysRestoreOptions) -> Result<String, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());
    let mut chain = CosmosSdkChain::bootstrap(opts.config, rt)?;

    let key = add_key_mnemonic(chain.keybase_mut(), &opts.mnemonic)?;

    Ok(format!(
        "Restored key '{}' ({}) on chain {}",
        opts.name,
        key.account,
        chain.id()
    ))
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
