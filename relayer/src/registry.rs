//! Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.

use std::{collections::HashMap, sync::Arc};

use tokio::runtime::Runtime as TokioRuntime;
use tracing::trace;

use ibc::ics24_host::identifier::ChainId;

use crate::{
    chain::{handle::ChainHandle, runtime::ChainRuntime, CosmosSdkChain},
    config::Config,
};

/// Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.
///
/// The purpose of this type is to avoid spawning multiple runtimes for a single `ChainId`.
pub struct Registry {
    rt: Arc<TokioRuntime>,
    config: Config,
    handles: HashMap<ChainId, Box<dyn ChainHandle>>,
}

impl Registry {
    /// Construct a new [`Registry`] using the provided [`Config`]
    pub fn new(config: Config) -> Self {
        Self {
            rt: Arc::new(TokioRuntime::new().unwrap()),
            config,
            handles: HashMap::new(),
        }
    }

    /// Return the size of the registry, i.e., the number of distinct chain runtimes.
    pub fn size(&self) -> usize {
        self.handles.len()
    }

    /// Get the [`ChainHandle`] associated with the given [`ChainId`].
    ///
    /// If there is no handle yet, this will first spawn the runtime and then
    /// return its handle.
    pub fn get_or_spawn(
        &mut self,
        chain_id: &ChainId,
    ) -> Result<Box<dyn ChainHandle>, Box<dyn std::error::Error>> {
        if !self.handles.contains_key(chain_id) {
            let handle = spawn_chain_runtime(&self.config, chain_id, self.rt.clone())?;
            self.handles.insert(chain_id.clone(), handle);
            trace!("spawned chain runtime for chain identifier {}", chain_id);
        }

        let handle = self.handles.get(chain_id).unwrap();

        Ok(handle.clone())
    }
}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(
    config: &Config,
    chain_id: &ChainId,
    rt: Arc<TokioRuntime>,
) -> Result<Box<dyn ChainHandle>, Box<dyn std::error::Error>> {
    let chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| format!("missing chain for id ({}) in configuration file", chain_id))?;

    let (handle, _) = ChainRuntime::<CosmosSdkChain>::spawn(chain_config, rt)?;

    Ok(handle)
}
