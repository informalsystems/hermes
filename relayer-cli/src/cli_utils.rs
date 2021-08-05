use std::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    chain::{
        handle::{ChainHandle, ProdChainHandle},
        runtime::ChainRuntime,
        CosmosSdkChain,
    },
    config::Config,
};

use crate::error::Error;

#[derive(Clone, Debug)]
/// Pair of chain handles that are used by most CLIs.
pub struct ChainHandlePair<Chain: ChainHandle = ProdChainHandle> {
    /// Source chain handle
    pub src: Chain,
    /// Destination chain handle
    pub dst: Chain,
}

impl<Chain: ChainHandle> ChainHandlePair<Chain> {
    /// Spawn the source and destination chain runtime from the configuration and chain identifiers,
    /// and return the pair of associated handles.
    pub fn spawn_generic(
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        let src = spawn_chain_runtime_generic(config, src_chain_id)?;
        let dst = spawn_chain_runtime_generic(config, dst_chain_id)?;

        Ok(ChainHandlePair { src, dst })
    }
}

impl ChainHandlePair<ProdChainHandle> {
    pub fn spawn(
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        Self::spawn_generic(config, src_chain_id, dst_chain_id)
    }
}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(config: &Config, chain_id: &ChainId) -> Result<impl ChainHandle, Error> {
    spawn_chain_runtime_generic::<ProdChainHandle>(config, chain_id)
}

pub fn spawn_chain_runtime_generic<Chain: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
) -> Result<Chain, Error> {
    let chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| Error::missing_config(chain_id.clone()))?;

    let rt = Arc::new(TokioRuntime::new().unwrap());
    let handle =
        ChainRuntime::<CosmosSdkChain>::spawn::<Chain>(chain_config, rt).map_err(Error::relayer)?;

    Ok(handle)
}
