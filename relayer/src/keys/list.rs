use std::sync::{Arc, Mutex};

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::KeyRingOperations;

#[derive(Clone, Debug)]
pub struct KeysListOptions {
    pub chain_config: ChainConfig,
}

pub fn list_keys(opts: KeysListOptions) -> Result<String, Error> {
    let rt = TokioRuntime::new().unwrap();

    // Get the destination chain
    let chain = CosmosSDKChain::bootstrap(opts.chain_config, Arc::new(Mutex::new(rt)))?;

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
