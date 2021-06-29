use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use serde::{Deserialize, Serialize};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::channel::ChannelEnd;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::chain::{Chain, CosmosSdkChain};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryChannelEndsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,

    #[options(help = "display result in summary form", short = "s")]
    summary: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceResult {
    channel_end: ChannelEnd,
    connection_end: ConnectionEnd,
    client_state: ClientState,
    counterparty_channel_end: ChannelEnd,
    counterparty_connection_end: ConnectionEnd,
    counterparty_client_state: ClientState,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceSummary {
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

fn do_run(cmd: &QueryChannelEndsCmd) -> Result<(), Box<dyn std::error::Error>> {
    debug!("Options: {:?}", cmd);

    let config = app_config();

    let chain_id = cmd.chain_id.clone();
    let port_id = cmd.port_id.clone();
    let channel_id = cmd.channel_id.clone();

    let chain_config = config
        .find_chain(&chain_id)
        .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

    let rt = Arc::new(TokioRuntime::new()?);
    let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt.clone())?;

    // let chain = spawn_chain_runtime(&config, &chain_id)?;

    let chain_height = match cmd.height {
        Some(height) => Height::new(chain.id().version(), height),
        None => chain.query_latest_height()?,
    };

    let channel_end = chain.query_channel(&port_id, &channel_id, chain_height)?;

    let connection_id = channel_end
        .connection_hops
        .first()
        .ok_or_else(|| format!("missing connection_hops for channel {}", channel_id))?
        .clone();

    let connection_end = chain.query_connection(&connection_id, chain_height)?;

    let client_id = connection_end.client_id().clone();

    let client_state = chain.query_client_state(&client_id, chain_height)?;

    let channel_counterparty = channel_end.counterparty().clone();
    let connection_counterparty = connection_end.counterparty().clone();

    let counterparty_client_id = connection_counterparty.client_id().clone();

    let counterparty_connection_id = connection_counterparty.connection_id.ok_or_else(|| {
        format!(
            "connection end do not have counterparty connection id: {:?}",
            connection_end
        )
    })?;

    let counterparty_port_id = channel_counterparty.port_id().clone();

    let counterparty_channel_id = channel_counterparty.channel_id.ok_or_else(|| {
        format!(
            "channel end do not have counterparty channel id: {:?}",
            channel_end
        )
    })?;

    let counterparty_chain_id = client_state.chain_id.clone();

    let chain_config_b = config.find_chain(&counterparty_chain_id).ok_or_else(|| {
        format!(
            "chain '{}' not found in configuration file",
            counterparty_chain_id
        )
    })?;

    let counterparty_chain = CosmosSdkChain::bootstrap(chain_config_b.clone(), rt)?;

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

    if cmd.summary {
        let res = TraceSummary {
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
    } else {
        let res = TraceResult {
            channel_end,
            connection_end,
            client_state,

            counterparty_channel_end,
            counterparty_connection_end,
            counterparty_client_state,
        };

        Output::success(res).exit();
    }

    Ok(())
}

impl Runnable for QueryChannelEndsCmd {
    fn run(&self) {
        match do_run(self) {
            Ok(()) => {}
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
