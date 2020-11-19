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
pub struct KeysListOptions {
    pub chain_config: ChainConfig,
}

pub fn list_keys(opts: KeysListOptions) -> Result<String, Error> {
    // Get the destination chain
    let chain = CosmosSDKChain::from_config(opts.chain_config)?;

    let key_entry = chain.keybase().get_key();

    match key_entry {
        Ok(k) => Ok(format!(
            "chain: {} -> {} ({})",
            chain.config().id.clone(),
            chain.config().key_name.clone(),
            k.account.as_str(),
        )),
        Err(e) => Err(Kind::KeyBase.context(e).into()),
    }
}
