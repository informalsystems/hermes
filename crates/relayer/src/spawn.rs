use alloc::sync::Arc;

use flex_error::define_error;
use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::{
    chain::{cosmos::CosmosSdkChain, endpoint::ChainEndpoint, handle::ChainHandle, ChainType},
    config::{ChainConfig, Config},
    error::Error as RelayerError,
};

define_error! {
    SpawnError {
        Relayer
            [ RelayerError ]
            | _ | { "relayer error" },

        RuntimeNotFound
            | _ | { "expected runtime to be found in registry" },

        MissingChainConfig
            { chain_id: ChainId }
            | e | {
                format_args!("missing chain config for '{}' in configuration file", e.chain_id)
            },
    }
}

impl SpawnError {
    pub fn log_as_debug(&self) -> bool {
        self.detail().log_as_debug()
    }
}

impl SpawnErrorDetail {
    pub fn log_as_debug(&self) -> bool {
        matches!(self, SpawnErrorDetail::MissingChainConfig(_))
    }
}

pub enum ChainImpl {
    CosmosSdk(CosmosSdkChain),
}

impl ChainImpl {
    pub fn config(&self) -> &ChainConfig {
        match self {
            Self::CosmosSdk(chain) => chain.config(),
        }
    }
}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime<Handle: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
    rt: Arc<TokioRuntime>,
) -> Result<Handle, SpawnError> {
    let chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| SpawnError::missing_chain_config(chain_id.clone()))?;

    let handle = match chain_config.r#type {
        ChainType::CosmosSdk => {
            let chain = CosmosSdkChain::bootstrap(chain_config, rt).map_err(SpawnError::relayer)?;
            let chain = ChainImpl::CosmosSdk(chain);
            Handle::new(Arc::new(chain))
        }
    };

    Ok(handle)
}
