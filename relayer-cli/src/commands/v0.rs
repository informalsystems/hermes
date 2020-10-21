use std::{ops::Deref, thread};

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use relayer::{
    chain::handle::ChainRuntime,
    channel::{Channel, ChannelConfig},
    connection::{Connection, ConnectionConfig},
    foreign_client::{ForeignClient, ForeignClientConfig},
    link::{Link, LinkConfig},
};

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

pub fn v0_task(_config: Config) -> Result<(), BoxError> {
    let src_chain = ChainRuntime::new(todo!()); // TODO: Pass chain config
    let dst_chain = ChainRuntime::new(todo!()); // TODO: Pass chain config

    let src_chain_handle = src_chain.handle();
    thread::spawn(move || {
        src_chain.run().unwrap();
    });

    let dst_chain_handle = dst_chain.handle();
    thread::spawn(move || {
        // What should we do on return here?
        dst_chain.run().unwrap();
    });

    // Another idea is to encode the semantic depency more explicitely as
    // foreign_client.new_connect(...).new_channel(...).new_link
    // I think this is actualy what we want
    // Think about how that would work with multiple links

    let foreign_client = ForeignClient::new(
        &src_chain_handle,
        &dst_chain_handle,
        ForeignClientConfig::new(todo!(), todo!()),
    )?;

    let connection = Connection::new(
        &src_chain_handle,
        &dst_chain_handle,
        &foreign_client, // Create a semantic dependecy
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
        foreign_client, // Actual dependecy
        channel,        // Semantic dependecy
        LinkConfig::new(todo!(), todo!(), todo!()),
    )?;

    link.run()?;

    Ok(())
}
