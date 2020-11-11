use crate::chain::CosmosSDKChain;
use crate::config::ChainConfig;
use crate::error;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyRing, KeyRingOperations};
use std::fs;
use std::path::Path;

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<Vec<u8>, Error> {
    // TODO - Implement the logic to persist the key in the filesystem
    // Get the destination chain
    let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;

    // Check if the key file exists
    if fs::metadata(Path::new(&opts.file)).is_err() {
        return Err(Kind::KeyBase.context("error reading the key file, file does not exist").into());
    };

    let key_file_contents = fs::read_to_string(&opts.name).map_err(|e| Kind::KeyBase.context("error reading the key file"))?;

    let key_entry = chain.keybase.key_from_seed_file(&opts.file);

    match key_entry {
        Ok(k) => {
            chain
                .keybase
                .add(opts.name, k.clone())
                .map_err(|e| error::Kind::KeyBase.context(e))?;
            Ok(k.address)
        }
        Err(e) => {
            return Err(Kind::KeyBase.context("error reading the key file").into());
        }
    }
}
