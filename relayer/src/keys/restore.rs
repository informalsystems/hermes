use crate::chain::{runtime::ChainRuntime, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error;

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub name: String,
    pub mnemonic: String,
    pub chain_config: ChainConfig,
}

pub fn restore_key(opts: KeysRestoreOptions) -> eyre::Result<Vec<u8>> {
    // Get the destination chain
    let (chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(opts.chain_config)?;

    let address = chain
        .get_key()
        .map_err(|e| error::Kind::KeyBase.context(e))?;

    Ok(address.account.as_bytes().to_vec())
}
