use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use serde::{Deserialize, Serialize};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics04_channel::channel::ChannelEnd;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::{Chain, CosmosSdkChain};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryTraceCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CmdResult {
    pub channel_end_a: ChannelEnd,
    pub connection_end_a: ConnectionEnd,
    pub client_state_a: ClientState,

    pub channel_end_b: ChannelEnd,
    pub connection_end_b: ConnectionEnd,
    pub client_state_b: ClientState,
}

fn do_run(cmd: &QueryTraceCmd) -> Result<CmdResult, Box<dyn std::error::Error>> {
    debug!("Options: {:?}", cmd);

    let config = app_config();

    let chain_id_a = cmd.chain_id.clone();
    let port_id_a = cmd.port_id.clone();
    let channel_id_a = cmd.channel_id.clone();

    let chain_a_config = config
        .find_chain(&chain_id_a)
        .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id_a))?;

    let rt = Arc::new(TokioRuntime::new().unwrap());
    let chain_a = CosmosSdkChain::bootstrap(chain_a_config.clone(), rt.clone())?;

    let height = ibc::Height::new(chain_a.id().version(), cmd.height.unwrap_or(0_u64));

    let channel_end_a = chain_a.query_channel(&port_id_a, &channel_id_a, height)?;

    let connection_id_a = channel_end_a
        .connection_hops
        .first()
        .ok_or_else(|| format!("missing connection_hops"))?;

    let connection_end_a = chain_a.query_connection(connection_id_a, height)?;

    let client_state_a = chain_a.query_client_state(&connection_end_a.client_id(), height)?;

    let channel_counterparty = channel_end_a.counterparty().clone();
    let connection_counterparty = connection_end_a.counterparty().clone();

    let client_id_b = connection_counterparty.client_id().clone();

    let connection_id_b = connection_counterparty.connection_id.ok_or_else(|| {
        format!(
            "connection end do not have counterparty connection id: {:?}",
            connection_end_a
        )
    })?;

    let port_id_b = channel_counterparty.port_id().clone();

    let channel_id_b = channel_counterparty.channel_id.ok_or_else(|| {
        format!(
            "channel end do not have counterparty channel id: {:?}",
            channel_end_a
        )
    })?;

    let chain_id_b = client_state_a.chain_id.clone();

    let chain_config_b = config
        .find_chain(&chain_id_b)
        .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id_b))?;

    let chain_b = CosmosSdkChain::bootstrap(chain_config_b.clone(), rt).unwrap();

    let connection_end_b = chain_b.query_connection(&connection_id_b, height)?;

    let client_state_b = chain_a.query_client_state(&client_id_b, Height::zero())?;

    let channel_end_b = chain_a.query_channel(&port_id_b, &channel_id_b, Height::zero())?;

    Ok(CmdResult {
        channel_end_a,
        connection_end_a,
        client_state_a,

        channel_end_b,
        connection_end_b,
        client_state_b,
    })
}

impl Runnable for QueryTraceCmd {
    fn run(&self) {
        match do_run(self) {
            Ok(res) => Output::success(res).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
