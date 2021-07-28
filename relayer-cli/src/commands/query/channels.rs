use std::sync::Arc;

use abscissa_core::{Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics04_channel::channel::State;
use ibc::ics24_host::identifier::{ChainId, PortChannelId};
use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;
use ibc_relayer::chain::{Chain, CosmosSdkChain};

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

fn run_query_channels(cmd: &QueryChannelsCmd) -> Result<(), Box<dyn std::error::Error>> {
    debug!("Options: {:?}", cmd);

    let mut output = vec![];
    let mut output_verbose = vec![];

    let config = app_config();
    let chain_id = cmd.chain_id.clone();

    let chain_config = config
        .find_chain(&chain_id)
        .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

    let rt = Arc::new(TokioRuntime::new()?);
    let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt.clone())?;
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
        let counterparty_chain_id = client_state.chain_id.clone();

        match &cmd.destination_chain {
            Some(dst_chain_id) if dst_chain_id != &counterparty_chain_id => {
                continue;
            }
            _ => { /* proceed */ }
        }

        if !cmd.verbose {
            output.push(PortChannelId {
                channel_id,
                port_id,
            });
        } else {
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

            let chain_config_b = config.find_chain(&counterparty_chain_id).ok_or_else(|| {
                format!(
                    "counterparty chain '{}' not found in configuration file",
                    counterparty_chain_id
                )
            })?;

            let counterparty_chain = CosmosSdkChain::bootstrap(chain_config_b.clone(), rt.clone())?;
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

            output_verbose.push(ChannelEnds {
                channel_end,
                connection_end,
                client_state,

                counterparty_channel_end,
                counterparty_connection_end,
                counterparty_client_state,
            });
        }
    }

    if !cmd.verbose {
        Output::success(output).exit();
    } else {
        Output::success(output_verbose).exit();
    }

    Ok(())
}

impl Runnable for QueryChannelsCmd {
    fn run(&self) {
        match run_query_channels(self) {
            Ok(()) => {}
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
