use std::sync::Arc;

use tokio::runtime::Runtime as TokioRuntime;

use crate::chain::CosmosSDKChain;
use crate::config::ChainConfig;
use crate::error;
use crate::error::Error;
use crate::keyring::store::KeyRingOperations;

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub name: String,
    pub mnemonic: String,
    pub chain_config: ChainConfig,
}

pub fn restore_key(opts: KeysRestoreOptions) -> Result<Vec<u8>, Error> {
    let rt = TokioRuntime::new().unwrap();

    // Get the destination chain
    let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config, Arc::new(rt))?;

    let address = chain
        .key_ring()
        .add_from_mnemonic(&opts.mnemonic)
        .map_err(|e| error::Kind::KeyBase.context(e))?;

    Ok(address.account.as_bytes().to_vec())
}
