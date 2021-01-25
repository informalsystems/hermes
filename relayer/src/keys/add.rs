use std::sync::Arc;

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::KeyRingOperations;
use std::fs;

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    let rt = TokioRuntime::new().unwrap();

    // Get the destination chain
    let chain = CosmosSDKChain::bootstrap(opts.clone().chain_config, Arc::new(rt))?;

    let key_contents = fs::read_to_string(&opts.file)
        .map_err(|_| Kind::KeyBase.context("error reading the key file"))?;

    // Check if it's a valid Key seed file
    let key_entry = chain.keybase().key_from_seed_file(&key_contents);

    match key_entry {
        Ok(k) => {
            chain
                .keybase()
                .add_key(key_contents.as_str())
                .map_err(|e| error::Kind::KeyBase.context(e))?;
            Ok(format!(
                "Added key {} ({}) on {} chain",
                opts.name.as_str(),
                k.account.as_str(),
                chain.id().clone()
            ))
        }
        Err(e) => Err(Kind::KeyBase.context(e).into()),
    }
}
