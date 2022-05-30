use core::fmt::{Debug, Error, Formatter};

use abscissa_core::clap::Parser;
use abscissa_core::Runnable;
use serde::Serialize;

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics04_channel::channel::{ChannelEnd, State};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::chain::requests::{
    PageRequest, QueryChannelRequest, QueryChannelsRequest, QueryClientStateRequest,
    QueryConnectionRequest,
};
use ibc_relayer::registry::Registry;

use crate::commands::query::channel_ends::ChannelEnds;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryChannelsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(
        short = 'd',
        long,
        help = "identifier of the channel's destination chain"
    )]
    destination_chain: Option<ChainId>,

    #[clap(
        short = 'v',
        long,
        help = "enable verbose output, displaying all client and connection ids"
    )]
    verbose: bool,
}

fn run_query_channels<Chain: ChainHandle>(
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

    let mut registry = <Registry<Chain>>::new((*config).clone());
    let chain = registry.get_or_spawn(&cmd.chain_id)?;
    let chain_height = chain.query_latest_height()?;

    let identified_channels = chain.query_channels(QueryChannelsRequest {
        pagination: Some(PageRequest::all()),
    })?;

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

        if cmd.verbose {
            let channel_ends = query_channel_ends(
                &mut registry,
                &chain,
                cmd.destination_chain.as_ref(),
                channel_end,
                connection_id,
                chain_id,
                port_id,
                channel_id,
                chain_height,
            );

            match channel_ends {
                Ok(channel_ends) => output.push_verbose(channel_ends),
                Err(e) => error!("failed to query channel ends: {}", e),
            }
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
fn query_channel_ends<Chain: ChainHandle>(
    registry: &mut Registry<Chain>,
    chain: &Chain,
    destination_chain: Option<&ChainId>,
    channel_end: ChannelEnd,
    connection_id: ConnectionId,
    chain_id: ChainId,
    port_id: PortId,
    channel_id: ChannelId,
    chain_height: Height,
) -> Result<ChannelEnds, Box<dyn std::error::Error>> {
    let connection_end = chain.query_connection(QueryConnectionRequest {
        connection_id: connection_id.clone(),
        height: chain_height,
    })?;
    let client_id = connection_end.client_id().clone();
    let client_state = chain.query_client_state(QueryClientStateRequest {
        client_id,
        height: chain_height,
    })?;
    let counterparty_chain_id = client_state.chain_id();

    if let Some(dst_chain_id) = destination_chain {
        if dst_chain_id != &counterparty_chain_id {
            return Err(format!(
                "mismatch between supplied destination chain ({}) and counterparty chain ({})",
                dst_chain_id, counterparty_chain_id
            )
            .into());
        }
    }

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

    let counterparty_connection_end =
        counterparty_chain.query_connection(QueryConnectionRequest {
            connection_id: counterparty_connection_id,
            height: counterparty_chain_height,
        })?;

    let counterparty_client_state =
        counterparty_chain.query_client_state(QueryClientStateRequest {
            client_id: counterparty_client_id,
            height: counterparty_chain_height,
        })?;

    let counterparty_channel_end = counterparty_chain.query_channel(QueryChannelRequest {
        port_id: counterparty_port_id,
        channel_id: counterparty_channel_id,
        height: counterparty_chain_height,
    })?;

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
        match run_query_channels::<BaseChainHandle>(self) {
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
