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
    // TODO - change the config to use typed Ids and same with ConnectionConfig, ClientConfig, ChannelConfig, etc
    let conn = &config
        .connections
        .clone()
        .ok_or("No connections configured")?[0];

    let path = &conn.paths.clone().ok_or("No paths configured")?[0];

    let connection = ConnectionConfig::new(&conn.clone())?;
    let channel = ChannelConfig::new(&connection, &path)?;

    let src_chain_config = config
        .chains
        .clone()
        .into_iter()
        .find(|c| c.id == connection.src().chain_id().clone())
        .ok_or("Configuration for source chain not found")?;

    let dst_chain_config = config
        .chains
        .clone()
        .into_iter()
        .find(|c| c.id == connection.dst().chain_id().clone())
        .ok_or("Configuration for source chain not found")?;

    let (src_chain_handle, _) = ChainRuntime::spawn(src_chain_config)?;
    let (dst_chain_handle, _) = ChainRuntime::spawn(dst_chain_config)?;

    Ok(channel_relay(
        src_chain_handle,
        dst_chain_handle,
        connection,
        channel,
    )?)
}
