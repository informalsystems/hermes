use std::fs;
use std::sync::{Arc, Mutex};

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error;
use crate::error::Kind;
use crate::keyring::store::KeyRingOperations;
use eyre::WrapErr;

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> eyre::Result<String> {
    let rt = TokioRuntime::new().unwrap();

    // Get the destination chain
    let chain = CosmosSDKChain::bootstrap(opts.clone().chain_config, Arc::new(Mutex::new(rt)))?;

    let key_contents = fs::read_to_string(&opts.file).wrap_err(Kind::KeyBase)?;

    //Check if it's a valid Key seed file
    let key_entry = chain.keybase().key_from_seed_file(&key_contents)?;

    chain
        .keybase()
        .add_key(key_contents.as_str())
        .wrap_err(error::Kind::KeyBase)?;
    Ok(format!(
        "Added key {} ({}) on {} chain",
        opts.name.as_str(),
        key_entry.account.as_str(),
        chain.id().clone()
    ))
}
