use std::fmt::{Debug, Error, Formatter};

use abscissa_core::{Options, Runnable};
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::Height;
use serde::Serialize;

use ibc::ics02_client::client_state::{AnyClientState, ClientState};
use ibc::ics04_channel::channel::{ChannelEnd, State};
use ibc::ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortChannelId, PortId};
use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;
use ibc_relayer::registry::Registry;

use crate::commands::query::channel_ends::ChannelEnds;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryChannelsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(help = "identifier of the channel's destination chain", short = "d")]
    destination_chain: Option<ChainId>,

    #[options(
        help = "enable verbose output, displaying all client and connection ids",
        short = "v"
    )]
    verbose: bool,
}

fn run_query_channels(
    cmd: &QueryChannelsCmd,
) -> Result<QueryChannelsOutput, Box<dyn std::error::Error>> {
    debug!("Options: {:?}", cmd);

    let mut output = if cmd.verbose {
        QueryChannelsOutput::verbose()
    } else {
        QueryChannelsOutput::summary()
    };

    let config = app_config();
    let chain_id = cmd.chain_id.clone();

    let mut registry = Registry::from_owned((*config).clone());
    let chain = registry.get_or_spawn(&cmd.chain_id)?;
    let chain_height = chain.query_latest_height()?;

    let req = QueryChannelsRequest {
        pagination: ibc_proto::cosmos::base::query::pagination::all(),
    };

    let identified_channels = chain.query_channels(req)?;

    for identified_channel in identified_channels {
        let port_id = identified_channel.port_id;
        let channel_id = identified_channel.channel_id;
        let chain_id = chain_id.clone();
        let channel_end = identified_channel.channel_end;

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
        let counterparty_chain_id = client_state.chain_id();

        if let Some(dst_chain_id) = &cmd.destination_chain {
            if dst_chain_id != &counterparty_chain_id {
                continue;
            }
        }

        if cmd.verbose {
            let channel_ends = query_channel_ends(
                &mut registry,
                channel_end,
                connection_end,
                client_state,
                connection_id,
                chain_id,
                counterparty_chain_id,
                port_id,
                channel_id,
                chain_height,
            )?;

            output.push_verbose(channel_ends);
        } else {
            output.push_summary(PortChannelId {
                channel_id,
                port_id,
            });
        }
    }

    Ok(output)
}

#[allow(clippy::too_many_arguments)]
fn query_channel_ends(
    registry: &mut Registry,
    channel_end: ChannelEnd,
    connection_end: ConnectionEnd,
    client_state: AnyClientState,
    connection_id: ConnectionId,
    chain_id: ChainId,
    counterparty_chain_id: ChainId,
    port_id: PortId,
    channel_id: ChannelId,
    chain_height: Height,
) -> Result<ChannelEnds, Box<dyn std::error::Error>> {
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

    Ok(ChannelEnds {
        channel_end,
        connection_end,
        client_state,
        counterparty_channel_end,
        counterparty_connection_end,
        counterparty_client_state,
    })
}

impl Runnable for QueryChannelsCmd {
    fn run(&self) {
        match run_query_channels(self) {
            Ok(output) => Output::success(output).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Serialize)]
#[serde(untagged)]
enum QueryChannelsOutput {
    Verbose(Vec<ChannelEnds>),
    Summary(Vec<PortChannelId>),
}

impl QueryChannelsOutput {
    fn verbose() -> Self {
        Self::Verbose(Vec::new())
    }

    fn summary() -> Self {
        Self::Summary(Vec::new())
    }

    fn push_verbose(&mut self, ce: ChannelEnds) {
        assert!(matches!(self, Self::Verbose(_)));

        if let Self::Verbose(ref mut ces) = self {
            ces.push(ce);
        } else {
            unreachable!();
        }
    }

    fn push_summary(&mut self, pc: PortChannelId) {
        assert!(matches!(self, Self::Summary(_)));

        if let Self::Summary(ref mut pcs) = self {
            pcs.push(pc);
        } else {
            unreachable!();
        }
    }
}

impl Debug for QueryChannelsOutput {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            QueryChannelsOutput::Verbose(output) => write!(f, "{:#?}", output),
            QueryChannelsOutput::Summary(output) => write!(f, "{:#?}", output),
        }
    }
}
