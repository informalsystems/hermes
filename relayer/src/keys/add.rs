use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyRing, KeyRingOperations};
use futures::AsyncReadExt;
use std::fs;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<String, Error> {
    // Get the destination chain
    let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;

    let key_file_contents = fs::read_to_string(&opts.file)
        .map_err(|e| Kind::KeyBase.context("error reading the key file"))?;

    //Check if it's a valid Key seed file
    let key_entry = chain.keybase.key_from_seed_file(&key_file_contents);

    match key_entry {
        Ok(k) => {
            chain
                .keybase
                .add(
                    opts.name.as_str(),
                    key_file_contents.as_str(),
                    chain.config().id.clone().as_str(),
                )
                .map_err(|e| error::Kind::KeyBase.context(e))?;
            Ok(format!(
                "Added key: {} ({})",
                opts.name.as_str(),
                k.account.as_str()
            ))
        }
        Err(e) => Err(Kind::KeyBase.context(e).into()),
    }
}
