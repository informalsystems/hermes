use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::{Deserialize, Serialize};

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::{ChannelEnd, State};
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::chain::requests::{
    IncludeProof, QueryChannelRequest, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::registry::Registry;

use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryChannelEndsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "port",
        required = true,
        value_name = "PORT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the port to query"
    )]
    port_id: PortId,

    #[clap(
        long = "channel",
        visible_alias = "chan",
        required = true,
        value_name = "CHANNEL_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the channel to query"
    )]
    channel_id: ChannelId,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "Height of the state to query"
    )]
    height: Option<u64>,

    #[clap(
        long = "verbose",
        help = "Enable verbose output, displaying all details of channels, connections & clients"
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
    let config = app_config();

    let QueryChannelEndsCmd {
        chain_id,
        port_id,
        channel_id,
        ..
    } = cmd;

    let mut registry = <Registry<Chain>>::new((*config).clone());
    let chain = registry.get_or_spawn(chain_id)?;

    let chain_height = match cmd.height {
        Some(height) => {
            Height::new(chain.id().version(), height).unwrap_or_else(exit_with_unrecoverable_error)
        }
        None => chain.query_latest_height()?,
    };

    let (channel_end, _) = chain.query_channel(
        QueryChannelRequest {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            height: QueryHeight::Specific(chain_height),
        },
        IncludeProof::No,
    )?;
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

    let (connection_end, _) = chain.query_connection(
        QueryConnectionRequest {
            connection_id: connection_id.clone(),
            height: QueryHeight::Specific(chain_height),
        },
        IncludeProof::No,
    )?;

    let client_id = connection_end.client_id().clone();

    let (client_state, _) = chain.query_client_state(
        QueryClientStateRequest {
            client_id: client_id.clone(),
            height: QueryHeight::Specific(chain_height),
        },
        IncludeProof::No,
    )?;

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
    let counterparty_chain_height_query =
        QueryHeight::Specific(counterparty_chain.query_latest_height()?);

    let (counterparty_connection_end, _) = counterparty_chain.query_connection(
        QueryConnectionRequest {
            connection_id: counterparty_connection_id.clone(),
            height: counterparty_chain_height_query,
        },
        IncludeProof::No,
    )?;

    let (counterparty_client_state, _) = counterparty_chain.query_client_state(
        QueryClientStateRequest {
            client_id: counterparty_client_id.clone(),
            height: counterparty_chain_height_query,
        },
        IncludeProof::No,
    )?;

    let (counterparty_channel_end, _) = counterparty_chain.query_channel(
        QueryChannelRequest {
            port_id: counterparty_port_id.clone(),
            channel_id: counterparty_channel_id.clone(),
            height: counterparty_chain_height_query,
        },
        IncludeProof::No,
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
            chain_id: chain_id.clone(),
            client_id,
            connection_id,
            channel_id: channel_id.clone(),
            port_id: port_id.clone(),

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

#[cfg(test)]
mod tests {
    use super::QueryChannelEndsCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_query_channel_ends_required_only() {
        assert_eq!(
            QueryChannelEndsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: None,
                verbose: false
            },
            QueryChannelEndsCmd::parse_from(&[
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07"
            ])
        )
    }

    #[test]
    fn test_query_channel_ends_chan_alias() {
        assert_eq!(
            QueryChannelEndsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: None,
                verbose: false
            },
            QueryChannelEndsCmd::parse_from(&[
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--chan",
                "channel-07"
            ])
        )
    }

    #[test]
    fn test_query_channel_ends_height() {
        assert_eq!(
            QueryChannelEndsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: Some(42),
                verbose: false
            },
            QueryChannelEndsCmd::parse_from(&[
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_channel_ends_verbose() {
        assert_eq!(
            QueryChannelEndsCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: None,
                verbose: true
            },
            QueryChannelEndsCmd::parse_from(&[
                "test",
                "--chain",
                "chain_id",
                "--port",
                "port_id",
                "--channel",
                "channel-07",
                "--verbose"
            ])
        )
    }

    #[test]
    fn test_query_channel_client_no_chan() {
        assert!(QueryChannelEndsCmd::try_parse_from(&[
            "test", "--chain", "chain_id", "--port", "port_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_channel_client_no_port() {
        assert!(QueryChannelEndsCmd::try_parse_from(&[
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_channel_client_no_chain() {
        assert!(QueryChannelEndsCmd::try_parse_from(&[
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }
}
