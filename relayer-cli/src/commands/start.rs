use std::ops::Deref;

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use ibc::ics04_channel::channel::Order;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;
use relayer::config::Config;
use relayer::relay::relay_on_new_link;

use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct StartCmd {}

impl StartCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        debug!("launching command `start` for relayer v0 command");
        v0_task(&config)
    }
}

impl Runnable for StartCmd {
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

    let ordering = Order::default(); // TODO - add to config
    let path = conn.paths.clone().ok_or("No paths configured")?[0].clone();

    let src_chain_config = config
        .find_chain(&conn.a_chain)
        .cloned()
        .ok_or("Configuration for source chain not found")?;

    let dst_chain_config = config
        .find_chain(&conn.b_chain)
        .cloned()
        .ok_or("Configuration for source chain not found")?;

    let (src_chain_handle, _) = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config)?;
    let (dst_chain_handle, _) = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config)?;

    Ok(relay_on_new_link(
        src_chain_handle,
        dst_chain_handle,
        ordering,
        path,
    )?)
}
