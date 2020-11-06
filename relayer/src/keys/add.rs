use crate::chain::CosmosSDKChain;
use crate::config::ChainConfig;
use crate::error;
use crate::error::Error;
use crate::keyring::store::{KeyRing, KeyRingOperations};

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub file: String,
    pub chain_config: ChainConfig,
}

pub fn add_key(opts: KeysAddOptions) -> Result<Vec<u8>, Error> {
    // TODO - Implement the logic to persist the key in the filesystem
    // Get the destination chain
    // let mut chain = CosmosSDKChain::from_config(opts.clone().chain_config)?;
    Ok(vec![])
    // let address = chain
    //     .keybase
    //     .add_from_mnemonic(&opts.mnemonic)
    //     .map_err(|e| error::Kind::KeyBase.context(e))?;
    //
    // Ok(address.account.as_bytes().to_vec())
}
