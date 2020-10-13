use crate::chain::CosmosSDKChain;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub name: String,
    pub mnemonic: String,
    pub chain_config: ChainConfig,
}

pub fn restore_key(opts: KeysRestoreOptions) -> Result<(), Error> {
    // Get the destination chain
    let chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;
    Ok(())
}
