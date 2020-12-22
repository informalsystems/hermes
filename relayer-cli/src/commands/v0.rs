use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use relayer::chain::runtime::ChainRuntime;
use relayer::channel::ChannelConfig;
use relayer::connection::ConnectionConfig;
use relayer::relay::channel_relay;

use crate::config::Config;
use crate::prelude::*;
use relayer::chain::CosmosSDKChain;

#[derive(Command, Debug, Options)]
pub struct V0Cmd {}

impl V0Cmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        debug!("launching 'v0' command");
        v0_task(&config)
    }
}

impl Runnable for V0Cmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

pub fn v0_task(config: &Config) -> Result<(), BoxError> {
    // Relay for a single channel, first on the first connection in configuration
    let conn = &config
        .connections
        .clone()
        .ok_or("No connections configured")?[0];

    let path = &conn.paths.clone().ok_or("No paths configured")?[0];

    let connection_cfg = ConnectionConfig::new(&conn.clone())?;
    let channel_cfg = ChannelConfig::new(&connection_cfg, &path)?;

    let src_chain_config = config
        .chains
        .clone()
        .into_iter()
        .find(|c| c.id == connection_cfg.src().chain_id().clone())
        .ok_or("Configuration for source chain not found")?;

    let dst_chain_config = config
        .chains
        .clone()
        .into_iter()
        .find(|c| c.id == connection_cfg.dst().chain_id().clone())
        .ok_or("Configuration for source chain not found")?;

    let (src_chain_handle, _) = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)?;
    let (dst_chain_handle, _) = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)?;

    Ok(channel_relay(
        src_chain_handle,
        dst_chain_handle,
        channel_cfg,
    )?)
}
