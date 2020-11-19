use std::{ops::Deref, thread};

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use relayer::{
    chain::runtime::ChainRuntime,
    channel::{Channel, ChannelConfig},
    connection::{Connection, ConnectionConfig},
    foreign_client::{ForeignClient, ForeignClientConfig},
    link::{Link, LinkConfig},
};

use crate::config::Config;
use crate::prelude::*;
use ibc::ics24_host::identifier::ClientId;
use std::str::FromStr;

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
    let src_chain_config = config
        .chains
        .get(0)
        .ok_or("Configuration for source chain (position 0 in chains config) not found")?;

    let dst_chain_config = config
        .chains
        .get(1)
        .ok_or("Configuration for dest. chain (position 1 in chains config) not found")?;

    let src_chain = ChainRuntime::new(src_chain_config);
    let dst_chain = ChainRuntime::new(dst_chain_config);

    let src_chain_handle = src_chain.handle()?;
    thread::spawn(move || {
        // TODO: What should we do on return here? Probably unrecoverable error.
        src_chain.run().unwrap();
    });

    let dst_chain_handle = dst_chain.handle()?;
    thread::spawn(move || {
        dst_chain.run().unwrap();
    });

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

    // Instantiate the foreign client on the source chain.
    let client_on_src = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::new(client_src_id),
    )?;

    // Instantiate the foreign client on the destination chain.
    let client_on_dst = ForeignClient::new(
        &dst_chain_handle,
        &src_chain_handle,
        ForeignClientConfig::new(client_dst_id),
    )?;

    let connection = Connection::new(
        &src_chain_handle,
        &dst_chain_handle,
        &client_on_src, // Semantic dependency.
        ConnectionConfig::new(todo!(), todo!()),
    )
    .unwrap();

    let channel = Channel::new(
        &src_chain_handle,
        &dst_chain_handle,
        connection, // Semantic dependecy
        ChannelConfig::new(todo!(), todo!()),
    )
    .unwrap();

    let link = Link::new(
        src_chain_handle,
        dst_chain_handle,
        client_on_src, // Actual dependecy
        channel,       // Semantic dependecy
        LinkConfig::new(todo!(), todo!(), todo!()),
    )?;

    link.run()?;

    Ok(())
}
