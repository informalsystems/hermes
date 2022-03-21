//! Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.

use alloc::collections::btree_map::BTreeMap as HashMap;
use alloc::sync::Arc;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use flex_error::define_error;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::{trace, warn};

use ibc::core::ics24_host::identifier::ChainId;

use crate::util::lock::RwArc;
use crate::{
    chain::{handle::ChainHandle, runtime::ChainRuntime, CosmosSdkChain},
    config::Config,
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
                format_args!("missing chain config for '{}' in configuration file",
                    e.chain_id)
            }
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

/// Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.
///
/// The purpose of this type is to avoid spawning multiple runtimes for a single `ChainId`.
#[derive(Debug)]
pub struct Registry<Chain: ChainHandle> {
    config: Config,
    handles: HashMap<ChainId, Chain>,
    rt: Arc<TokioRuntime>,
}

#[derive(Clone)]
pub struct SharedRegistry<Chain: ChainHandle> {
    pub registry: RwArc<Registry<Chain>>,
}

impl<Chain: ChainHandle> Registry<Chain> {
    /// Construct a new [`Registry`] using the provided [`Config`]
    pub fn new(config: Config) -> Self {
        Self {
            config,
            handles: HashMap::new(),
            rt: Arc::new(TokioRuntime::new().unwrap()),
        }
    }

    /// Return the size of the registry, i.e., the number of distinct chain runtimes.
    pub fn size(&self) -> usize {
        self.handles.len()
    }

    /// Return an iterator overall the chain handles managed by the registry.
    pub fn chains(&self) -> impl Iterator<Item = &Chain> {
        self.handles.values()
    }

    /// Get the [`ChainHandle`] associated with the given [`ChainId`].
    ///
    /// If there is no handle yet, this will first spawn the runtime and then
    /// return its handle.
    pub fn get_or_spawn(&mut self, chain_id: &ChainId) -> Result<Chain, SpawnError> {
        self.spawn(chain_id)?;

        let handle = self
            .handles
            .get(chain_id)
            .expect("runtime was just spawned");

        Ok(handle.clone())
    }

    /// Spawn a chain runtime for the chain with the given [`ChainId`],
    /// only if the registry does not contain a handle for that runtime already.
    ///
    /// Returns whether or not the runtime was actually spawned.
    pub fn spawn(&mut self, chain_id: &ChainId) -> Result<bool, SpawnError> {
        if !self.handles.contains_key(chain_id) {
            let handle = spawn_chain_runtime(&self.config, chain_id, self.rt.clone())?;
            self.handles.insert(chain_id.clone(), handle);
            trace!("[{}] spawned chain runtime", chain_id);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Shutdown the runtime associated with the given chain identifier.
    pub fn shutdown(&mut self, chain_id: &ChainId) {
        if let Some(handle) = self.handles.remove(chain_id) {
            if let Err(e) = handle.shutdown() {
                warn!(chain.id = %chain_id, "chain runtime might have failed to shutdown properly: {}", e);
            }
        }
    }
}

impl<Chain: ChainHandle> SharedRegistry<Chain> {
    pub fn new(config: Config) -> Self {
        let registry = Registry::new(config);

        Self {
            registry: Arc::new(RwLock::new(registry)),
        }
    }

    pub fn get_or_spawn(&self, chain_id: &ChainId) -> Result<Chain, SpawnError> {
        self.registry.write().unwrap().get_or_spawn(chain_id)
    }

    pub fn spawn(&self, chain_id: &ChainId) -> Result<bool, SpawnError> {
        self.write().spawn(chain_id)
    }

    pub fn shutdown(&self, chain_id: &ChainId) {
        self.write().shutdown(chain_id)
    }

    pub fn write(&self) -> RwLockWriteGuard<'_, Registry<Chain>> {
        self.registry.write().unwrap()
    }

    pub fn read(&self) -> RwLockReadGuard<'_, Registry<Chain>> {
        self.registry.read().unwrap()
    }
}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime<Chain: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
    rt: Arc<TokioRuntime>,
) -> Result<Chain, SpawnError> {
    let chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| SpawnError::missing_chain_config(chain_id.clone()))?;

    let handle =
        ChainRuntime::<CosmosSdkChain>::spawn(chain_config, rt).map_err(SpawnError::relayer)?;

    Ok(handle)
}
