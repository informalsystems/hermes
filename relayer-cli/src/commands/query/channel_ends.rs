use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::{Deserialize, Serialize};

use ibc::core::ics02_client::client_state::{AnyClientState, ClientState};
use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::{ChannelEnd, State};
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::registry::Registry;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryChannelEndsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the port to query")]
    port_id: PortId,

    #[clap(required = true, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[clap(short = 'H', long, help = "height of the state to query")]
    height: Option<u64>,

    #[clap(
        short = 'v',
        long,
        help = "enable verbose output, displaying all details of channels, connections & clients"
    )]
    verbose: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChannelEnds {
    pub channel_end: ChannelEnd,
    pub connection_end: ConnectionEnd,
    pub client_state: AnyClientState,
    pub counterparty_channel_end: ChannelEnd,
    pub counterparty_connection_end: ConnectionEnd,
    pub counterparty_client_state: AnyClientState,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChannelEndsSummary {
    chain_id: ChainId,
    client_id: ClientId,
    connection_id: ConnectionId,
    channel_id: ChannelId,
    port_id: PortId,

    counterparty_chain_id: ChainId,
    counterparty_client_id: ClientId,
    counterparty_connection_id: ConnectionId,
    counterparty_channel_id: ChannelId,
    counterparty_port_id: PortId,
}

fn do_run<Chain: ChainHandle>(cmd: &QueryChannelEndsCmd) -> Result<(), Box<dyn std::error::Error>> {
    debug!("Options: {:?}", cmd);

    let config = app_config();

    let chain_id = cmd.chain_id.clone();
    let port_id = cmd.port_id.clone();
    let channel_id = cmd.channel_id;

    let mut registry = <Registry<Chain>>::new((*config).clone());
    let chain = registry.get_or_spawn(&chain_id)?;

    let chain_height = match cmd.height {
        Some(height) => Height::new(chain.id().version(), height),
        None => chain.query_latest_height()?,
    };

    let channel_end = chain.query_channel(&port_id, &channel_id, chain_height)?;
    if channel_end.state_matches(&State::Uninitialized) {
        return Err(format!(
            "{}/{} on chain {} @ {:?} is uninitialized",
            port_id, channel_id, chain_id, chain_height
        )
        .into());
    }

    let connection_id = channel_end
        .connection_hops
        .first()
        .ok_or_else(|| {
            format!(
                "missing connection_hops for {}/{} on chain {} @ {:?}",
                port_id, channel_id, chain_id, chain_height
            )
        })?
        .clone();

    let connection_end = chain.query_connection(&connection_id, chain_height)?;

    let client_id = connection_end.client_id().clone();

    let client_state = chain.query_client_state(&client_id, chain_height)?;

    let channel_counterparty = channel_end.counterparty().clone();
    let connection_counterparty = connection_end.counterparty().clone();

    let counterparty_client_id = connection_counterparty.client_id().clone();

    let counterparty_connection_id = connection_counterparty.connection_id.ok_or_else(|| {
        format!(
            "connection end for {} on chain {} @ {:?} does not have counterparty connection id: {:?}",
            connection_id,
            chain_id,
            chain_height,
            connection_end
        )
    })?;

    let counterparty_port_id = channel_counterparty.port_id().clone();

    let counterparty_channel_id = channel_counterparty.channel_id.ok_or_else(|| {
        format!(
            "channel end for {}/{} on chain {} @ {:?} does not have counterparty channel id: {:?}",
            port_id, channel_id, chain_id, chain_height, channel_end
        )
    })?;

    let counterparty_chain_id = client_state.chain_id();
    let counterparty_chain = registry.get_or_spawn(&counterparty_chain_id)?;
    let counterparty_chain_height = counterparty_chain.query_latest_height()?;

    let counterparty_connection_end = counterparty_chain
        .query_connection(&counterparty_connection_id, counterparty_chain_height)?;

    let counterparty_client_state = counterparty_chain
        .query_client_state(&counterparty_client_id, counterparty_chain_height)?;

    let counterparty_channel_end = counterparty_chain.query_channel(
        &counterparty_port_id,
        &counterparty_channel_id,
        counterparty_chain_height,
    )?;

    if cmd.verbose {
        let res = ChannelEnds {
            channel_end,
            connection_end,
            client_state,

            counterparty_channel_end,
            counterparty_connection_end,
            counterparty_client_state,
        };

        Output::success(res).exit();
    } else {
        let res = ChannelEndsSummary {
            chain_id,
            client_id,
            connection_id,
            channel_id,
            port_id,

            counterparty_chain_id,
            counterparty_client_id,
            counterparty_connection_id,
            counterparty_channel_id,
            counterparty_port_id,
        };

        Output::success(res).exit();
    }
}

impl Runnable for QueryChannelEndsCmd {
    fn run(&self) {
        match do_run::<BaseChainHandle>(self) {
            Ok(()) => {}
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
