use std::sync::Arc;

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::{Chain, CosmosSdkChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use std::fs;

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());

    // Get the destination chain
    let mut chain = CosmosSdkChain::bootstrap(opts.clone().chain_config, rt)?;

    let key_contents = fs::read_to_string(&opts.file)
        .map_err(|_| Kind::KeyBase.context("error reading the key file"))?;

    // Check if it's a valid Key seed file
    let key_entry = chain
        .keybase()
        .key_from_seed_file(&key_contents)
        .map_err(|e| Kind::KeyBase.context(e))?;

    chain
        .keybase_mut()
        .add_key(key_entry.clone())
        .map_err(|e| Kind::KeyBase.context(e))?;

    Ok(format!(
        "Added key '{}' ({}) on chain {}",
        opts.name.as_str(),
        key_entry.account.as_str(),
        chain.id().clone()
    ))
}
