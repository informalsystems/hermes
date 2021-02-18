use abscissa_core::config;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::chain::CosmosSDKChain;
use ibc_relayer::{chain::handle::ChainHandle, config::StoreConfig};
use ibc_relayer::{chain::runtime::ChainRuntime, config::ChainConfig};

use crate::application::CliApp;
use crate::error::{Error, Kind};

/// Pair of chain handlers that are used by most CLIs.
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
        spawn_chain_runtimes(options, config, src_chain_id, dst_chain_id)
    }
}

/// Spawn the source and destination chain runtime from the configuration and chain identifiers,
/// and return the pair of associated handles.
fn spawn_chain_runtimes(
    spawn_options: SpawnOptions,
    config: &config::Reader<CliApp>,
    src_chain_id: &ChainId,
    dst_chain_id: &ChainId,
) -> Result<ChainHandlePair, Error> {
    let src_config = config
        .find_chain(src_chain_id)
        .cloned()
        .ok_or_else(|| "missing source chain in configuration file".to_string());

    let dst_config = config
        .find_chain(dst_chain_id)
        .cloned()
        .ok_or_else(|| "missing destination chain configuration file".to_string());

    let (mut src_chain_config, mut dst_chain_config) =
        zip_result(src_config, dst_config).map_err(|e| Kind::Config.context(e))?;

    spawn_options.apply(&mut src_chain_config);
    spawn_options.apply(&mut dst_chain_config);

    let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)
        .map_err(|e| Kind::Runtime.context(e));

    let src = src_chain_res.map(|(handle, _)| handle)?;

    let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)
        .map_err(|e| Kind::Runtime.context(e));

    let dst = dst_chain_res.map(|(handle, _)| handle)?;

    Ok(ChainHandlePair { src, dst })
}

pub fn spawn_chain_runtime(
    spawn_options: &SpawnOptions,
    config: &config::Reader<CliApp>,
    chain_id: &ChainId,
) -> Result<Box<dyn ChainHandle>, Error> {
    let mut chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| "missing destination chain configuration file".to_string())
        .map_err(|e| Kind::Config.context(e))?;

    spawn_options.apply(&mut chain_config);

    Ok(ChainRuntime::<CosmosSDKChain>::spawn(chain_config)
        .map_err(|e| Kind::Runtime.context(e))
        .map(|(handle, _)| handle)?)
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

/// Zip two results together.
fn zip_result<A, B, E>(a: Result<A, E>, b: Result<B, E>) -> Result<(A, B), E> {
    match (a, b) {
        (Ok(a), Ok(b)) => Ok((a, b)),
        (Err(e), _) | (_, Err(e)) => Err(e),
    }
}
