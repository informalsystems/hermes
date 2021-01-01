use std::sync::{Arc, Mutex};

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::keyring::store::KeyRingOperations;

#[derive(Clone, Debug)]
pub struct KeysListOptions {
    pub chain_config: ChainConfig,
}

pub fn list_keys(opts: KeysListOptions) -> eyre::Result<String> {
    let rt = TokioRuntime::new().unwrap();

    // Get the destination chain
    let chain = CosmosSDKChain::bootstrap(opts.chain_config, Arc::new(Mutex::new(rt)))?;

    let key_entry = chain.keybase().get_key()?;

    Ok(format!(
        "chain: {} -> {} ({})",
        chain.config().id.clone(),
        chain.config().key_name.clone(),
        key_entry.account.as_str(),
    ))
}
