//! Various utilities for the Hermes CLI

use alloc::sync::Arc;

use tokio::runtime::Runtime as TokioRuntime;

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

use ibc_relayer::{
    chain::{
        counterparty::{channel_connection_client, ChannelConnectionClient},
        handle::{BaseChainHandle, ChainHandle},
    },
    config::Config,
    spawn,
};

use crate::error::Error;

#[derive(Clone, Debug)]
/// Pair of chain handles that are used by most CLIs.
pub struct ChainHandlePair<Chain: ChainHandle = BaseChainHandle> {
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

impl ChainHandlePair<BaseChainHandle> {
    pub fn spawn(
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        Self::spawn_generic(config, src_chain_id, dst_chain_id)
    }
}

/// Spawns a chain runtime for the chain in the configuration identified by given a chain identifier.
///
/// This function will use the default [`ChainHandle`] implementation, ie. the [`BaseChainHandle`].
///
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(config: &Config, chain_id: &ChainId) -> Result<impl ChainHandle, Error> {
    spawn_chain_runtime_generic::<BaseChainHandle>(config, chain_id)
}

/// Spawns a chain runtime for the chain in the configuraiton identified by the given chain identifier.
///
/// The `Handle` type parameter allows choosing which kind of [`ChainHandle`] implementation to use.
///
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime_generic<Handle: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
) -> Result<Handle, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());
    spawn::spawn_chain_runtime(config, chain_id, rt).map_err(Error::spawn)
}

/// Spawns a chain runtime for specified chain identifier, queries the counterparty chain associated
/// with specified port and channel id, and spawns a chain runtime for the counterparty chain.
///
/// The `Handle` type parameter allows choosing which kind of `ChainHandle` implementation to use.
///
/// Returns a tuple with a pair of associated chain handles and the ChannelEnd
pub fn spawn_chain_counterparty<Chain: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<(ChainHandlePair<Chain>, ChannelConnectionClient), Error> {
    let chain = spawn_chain_runtime_generic::<Chain>(config, chain_id)?;
    let channel_connection_client =
        channel_connection_client(&chain, port_id, channel_id).map_err(Error::supervisor)?;
    let counterparty_chain = {
        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        spawn_chain_runtime_generic::<Chain>(config, &counterparty_chain_id)?
    };

    Ok((
        ChainHandlePair {
            src: chain,
            dst: counterparty_chain,
        },
        channel_connection_client,
    ))
}
