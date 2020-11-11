use crate::chain::CosmosSDKChain;
use crate::config::ChainConfig;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyRing, KeyRingOperations};
use std::fs;
use std::path::Path;
use futures::AsyncReadExt;

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    // TODO - Implement the logic to persist the key in the filesystem
    // Get the destination chain
    let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;

    let file = Path::new(&opts.file);

    if !file.exists() {
        return Err(Kind::Store.context("cannot find key file specified".to_string()))?;
    }

    let key_file_contents = fs::read_to_string(&file).map_err(|e| Kind::KeyBase.context("error reading the key file"))?;

    let key_entry = chain.keybase.key_from_seed_file(&key_file_contents);

    match key_entry {
        Ok(k) => {
            chain
                .keybase
                .add(opts.name.clone(), k.clone())
                .map_err(|e| error::Kind::KeyBase.context(e))?;
            Ok(format!("Added {} key - Account: {}", opts.name.as_str(), k.account.as_str()))
        }
        Err(e) => {
            return Err(Kind::KeyBase.context(e).into());
        }
    }
}
