use std::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics02_client::client_state::ClientState;
use ibc::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::chain::counterparty::channel_connection_client;
use ibc_relayer::{
    chain::{handle::ChainHandle, runtime::ChainRuntime, CosmosSdkChain},
    config::Config,
};

use crate::error::{Error, Kind};

#[derive(Clone, Debug)]
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
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        let src = spawn_chain_runtime(config, src_chain_id)?;
        let dst = spawn_chain_runtime(config, dst_chain_id)?;

        Ok(ChainHandlePair { src, dst })
    }
}

/// Spawns a chain runtime from the configuration and given a chain identifier.
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(
    config: &Config,
    chain_id: &ChainId,
) -> Result<Box<dyn ChainHandle>, Error> {
    let chain_config = config
        .find_chain(chain_id)
        .cloned()
        .ok_or_else(|| format!("missing chain for id ({}) in configuration file", chain_id))
        .map_err(|e| Kind::Config.context(e))?;

    let rt = Arc::new(TokioRuntime::new().unwrap());
    let handle = ChainRuntime::<CosmosSdkChain>::spawn(chain_config, rt)
        .map_err(|e| Kind::Runtime.context(e))?;

    Ok(handle)
}

pub fn spawn_chain_counterparty(
    config: &Config,
    chain_id: &ChainId,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<(ChainHandlePair, IdentifiedChannelEnd), Error> {
    let chain = spawn_chain_runtime(config, chain_id)?;
    let channel_connection_client = channel_connection_client(chain.as_ref(), port_id, channel_id)
        .map_err(|e| Kind::Query.context(e))?;
    let counterparty_chain = {
        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        spawn_chain_runtime(config, &counterparty_chain_id)?
    };

    Ok((
        ChainHandlePair {
            src: chain,
            dst: counterparty_chain,
        },
        channel_connection_client.channel,
    ))
}
