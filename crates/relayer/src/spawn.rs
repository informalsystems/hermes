use alloc::sync::Arc;

use flex_error::define_error;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tokio::runtime::Runtime as TokioRuntime;

use crate::{
    chain::{
        astria::AstriaEndpoint,
        cosmos::CosmosSdkChain,
        handle::ChainHandle,
        runtime::ChainRuntime,
    },
    config::{
        ChainConfig,
        Config,
    },
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

    spawn_chain_runtime_with_config(chain_config, rt)
}

/// Spawns a chain runtime from the configuration and given a chain identifier,
/// allowing the caller to modify the chain config.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime_with_modified_config<Handle: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
    rt: Arc<TokioRuntime>,
    modify: impl FnOnce(&mut ChainConfig),
) -> Result<Handle, SpawnError> {
    let mut chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| SpawnError::missing_chain_config(chain_id.clone()))?;

    modify(&mut chain_config);

    spawn_chain_runtime_with_config(chain_config, rt)
}

/// Spawns a chain runtime from the given chain configuration
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime_with_config<Handle: ChainHandle>(
    config: ChainConfig,
    rt: Arc<TokioRuntime>,
) -> Result<Handle, SpawnError> {
    let handle = match config {
        ChainConfig::CosmosSdk(_) => ChainRuntime::<CosmosSdkChain>::spawn(config, rt),
        ChainConfig::Astria(_) => ChainRuntime::<AstriaEndpoint>::spawn(config, rt),
    }
    .map_err(SpawnError::relayer)?;

    Ok(handle)
}
