use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use relayer::chain::runtime::ChainRuntime;

use ibc::ics24_host::identifier::ClientId;
use std::str::FromStr;

use crate::config::Config;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct V0Cmd {}

impl V0Cmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        debug!("launching 'v0' command");
        v0_task(config)
    }
}

impl Runnable for V0Cmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

pub fn v0_task(config: Config) -> Result<(), BoxError> {
    // Load source and destination chains configurations
    let src_chain_config = config
        .chains
        .get(0)
        .cloned()
        .ok_or("Configuration for source chain (position 0 in chains config) not found")?;

    let dst_chain_config = config
        .chains
        .get(1)
        .cloned()
        .ok_or("Configuration for dest. chain (position 1 in chains config) not found")?;

    // Parse & validate client identifiers
    let client_src_id = ClientId::from_str(
        src_chain_config
            .client_ids
            .get(0)
            .ok_or("Config for client on source chain not found")?,
    )
    .map_err(|e| format!("Error validating client identifier for src chain ({:?})", e))?;

    let client_dst_id = ClientId::from_str(
        dst_chain_config
            .client_ids
            .get(0)
            .ok_or("Config for client for dest. chain not found")?,
    )
    .map_err(|e| format!("Error validating client identifier for dst chain ({:?})", e))?;

    // Initialize the source and destination runtimes and light clients
    let (src_chain_handle, _) = ChainRuntime::spawn(src_chain_config)?;
    let (dst_chain_handle, _) = ChainRuntime::spawn(dst_chain_config)?;

    // Instantiate the foreign client on the source chain.
    // let client_on_src = ForeignClient::new(
    //     &src_chain_handle,
    //     &dst_chain_handle,
    //     ForeignClientConfig::new(client_src_id),
    // )?;

    // Instantiate the foreign client on the destination chain.
    // let client_on_dst = ForeignClient::new(
    //     &dst_chain_handle,
    //     &src_chain_handle,
    //     ForeignClientConfig::new(client_dst_id),
    // )?;

    // Initialize a connection between the two chains
    // let connection = Connection::new(
    //     &src_chain_handle,
    //     &dst_chain_handle,
    //     &client_on_src, // Semantic dependency.
    //     ConnectionConfig::new(todo!(), todo!()),
    // )?;

    // Initialize a channel over the connection
    // let channel = Channel::new(
    //     &src_chain_handle,
    //     &dst_chain_handle,
    //     connection, // Semantic dependecy
    //     ChannelConfig::new(todo!(), todo!()),
    // )?;

    // TODO: Re-enable `link` module in `relayer/src/lib.rs`
    // let link = Link::new(
    //     src_chain_handle,
    //     dst_chain_handle,
    //     client_on_src, // Actual dependecy
    //     channel,       // Semantic dependecy
    //     LinkConfig::new(todo!(), todo!(), todo!()),
    // )?;

    // link.run()?;

    Ok(())
}
