use abscissa_core::config;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::chain::CosmosSdkChain;
use ibc_relayer::util::Unrecoverable;
use ibc_relayer::{chain::handle::ChainHandle, config::StoreConfig};
use ibc_relayer::{chain::runtime::ChainRuntime, config::ChainConfig};

use crate::application::CliApp;
use crate::error::{Error, Kind};

/// Pair of chain handles that are used by most CLIs.
pub struct ChainHandlePair {
    /// Source chain handle
    pub src: Box<dyn ChainHandle>,
    /// Destination chain handle
    pub dst: Box<dyn ChainHandle>,
}

impl ChainHandlePair {
    /// Spawn the source and destination chain runtime from the configuration and chain identifiers,
    /// and return the pair of associated handles.
    pub fn spawn(
        config: &config::Reader<CliApp>,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        Self::spawn_with(Default::default(), config, src_chain_id, dst_chain_id)
    }

    /// Spawn the source and destination chain runtime from the configuration and chain identifiers,
    /// and return the pair of associated handles. Accepts a `SpawnOptions` argument, which
    /// is used to override each chain configuration before spawning its runtime.
    pub fn spawn_with(
        options: SpawnOptions,
        config: &config::Reader<CliApp>,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        let src = spawn_chain_runtime(options.clone(), config, src_chain_id)?;
        let dst = spawn_chain_runtime(options, config, dst_chain_id)?;

        Ok(ChainHandlePair { src, dst })
    }
}

impl Unrecoverable for ChainHandlePair {}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(
    spawn_options: SpawnOptions,
    config: &config::Reader<CliApp>,
    chain_id: &ChainId,
) -> Result<Box<dyn ChainHandle>, Error> {
    let mut chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| format!("missing chain for id ({}) in configuration file", chain_id))
        .map_err(|e| Kind::Config.context(e))?;

    spawn_options.apply(&mut chain_config);

    let chain_res =
        ChainRuntime::<CosmosSdkChain>::spawn(chain_config).map_err(|e| Kind::Runtime.context(e));

    let handle = chain_res.map(|(handle, _)| handle)?;

    Ok(handle)
}

/// Allows override the chain configuration just before
/// spawning a new runtime instance.
///
/// This is currently only used to override the configured
/// light client store for one-off commands which do not
/// need the disk-based store.
#[derive(Clone, Debug, Default)]
pub struct SpawnOptions {
    override_store_config: Option<StoreConfig>,
}

impl SpawnOptions {
    /// Override the light client store config with the provided config.
    pub fn override_store_config(store_config: StoreConfig) -> Self {
        Self {
            override_store_config: Some(store_config),
        }
    }

    /// Apply these options to the provided chain configuration.
    pub fn apply(&self, chain_config: &mut ChainConfig) {
        if let Some(store_config) = &self.override_store_config {
            Self::apply_store_config(chain_config, &store_config)
        }
    }

    fn apply_store_config(chain_config: &mut ChainConfig, store_config: &StoreConfig) {
        if let Some(peer_config) = chain_config.peers.as_mut() {
            for light_client in &mut peer_config.light_clients {
                light_client.store = store_config.clone();
            }
        }
    }
}
