//! Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.

use std::collections::HashMap;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{chain::handle::ChainHandle, config::Config};
use tracing::trace;

use crate::{cli_utils::spawn_chain_runtime, error::Error};

/// Registry for keeping track of [`ChainHandle`]s indexed by a `ChainId`.
///
/// The purpose of this type is to avoid spawning multiple runtimes for a single `ChainId`.
pub struct Registry<'a> {
    config: &'a Config,
    handles: HashMap<ChainId, Box<dyn ChainHandle>>,
}

impl<'a> Registry<'a> {
    /// Construct a new [`Registry`] using the provided [`Config`]
    pub fn new(config: &'a Config) -> Self {
        Self {
            config,
            handles: HashMap::new(),
        }
    }

    /// Get the [`ChainHandle`] associated with the given [`ChainId`].
    ///
    /// If there is no handle yet, this will first spawn the runtime and then
    /// return its handle.
    pub fn get_or_spawn(&mut self, chain_id: &ChainId) -> Result<Box<dyn ChainHandle>, Error> {
        if !self.handles.contains_key(chain_id) {
            let handle = spawn_chain_runtime(&self.config, chain_id)?;
            self.handles.insert(chain_id.clone(), handle);
            trace!("spawned chain runtime for chain identifier {}", chain_id);
        }

        let handle = self.handles.get(chain_id).unwrap();
        Ok(handle.clone())
    }
}
