use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryConnectionChannelsRequest, QueryConnectionRequest, QueryHeight,
};

use ibc_relayer_types::core::{
    ics03_connection::connection::State,
    ics24_host::identifier::ConnectionId,
    ics24_host::identifier::{ChainId, PortChannelId},
};
use ibc_relayer_types::Height;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryConnectionEndCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "connection",
        visible_alias = "conn",
        required = true,
        value_name = "CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the connection to query"
    )]
    connection_id: ConnectionId,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "Height of the state to query. Leave unspecified for latest height."
    )]
    height: Option<u64>,
}

// cargo run --bin hermes -- query connection end --chain ibc-test --connection connectionidone --height 3
impl Runnable for QueryConnectionEndCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_connection(
            QueryConnectionRequest {
                connection_id: self.connection_id.clone(),
                height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                    QueryHeight::Specific(
                        Height::new(chain.id().version(), revision_height)
                            .unwrap_or_else(exit_with_unrecoverable_error),
                    )
                }),
            },
            IncludeProof::No,
        );
        match res {
            Ok((connection_end, _)) => {
                if connection_end.state_matches(&State::Uninitialized) {
                    Output::error(format!(
                        "connection '{}' does not exist",
                        self.connection_id
                    ))
                    .exit()
                } else {
                    Output::success(connection_end).exit()
                }
            }
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Command for querying the channel identifiers associated with a connection.
/// Sample invocation:
/// `cargo run --bin hermes -- query connection channels ibc-0 connection-0`
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryConnectionChannelsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "connection",
        visible_alias = "conn",
        required = true,
        value_name = "CONNECTION_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the connection to query"
    )]
    connection_id: ConnectionId,
}

impl Runnable for QueryConnectionChannelsCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res: Result<_, Error> = chain
            .query_connection_channels(QueryConnectionChannelsRequest {
                connection_id: self.connection_id.clone(),
                pagination: Some(PageRequest::all()),
            })
            .map_err(Error::relayer);

        match res {
            Ok(channels) => {
                let ids: Vec<PortChannelId> = channels
                    .into_iter()
                    .map(|identified_channel| PortChannelId {
                        port_id: identified_channel.port_id,
                        channel_id: identified_channel.channel_id,
                    })
                    .collect();
                Output::success(ids).exit()
            }
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{QueryConnectionChannelsCmd, QueryConnectionEndCmd};

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ConnectionId};

    #[test]
    fn test_query_connection_channels() {
        assert_eq!(
            QueryConnectionChannelsCmd {
                chain_id: ChainId::from_string("chain_id"),
                connection_id: ConnectionId::from_str("connection_id").unwrap()
            },
            QueryConnectionChannelsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--connection",
                "connection_id"
            ])
        )
    }

    #[test]
    fn test_query_connection_channels_conn_alias() {
        assert_eq!(
            QueryConnectionChannelsCmd {
                chain_id: ChainId::from_string("chain_id"),
                connection_id: ConnectionId::from_str("connection_id").unwrap()
            },
            QueryConnectionChannelsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--conn",
                "connection_id"
            ])
        )
    }

    #[test]
    fn test_query_connection_channels_no_conn() {
        assert!(
            QueryConnectionChannelsCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err()
        )
    }

    #[test]
    fn test_query_connection_channels_no_chain() {
        assert!(QueryConnectionChannelsCmd::try_parse_from([
            "test",
            "--connection",
            "connection_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_connection_end_required_only() {
        assert_eq!(
            QueryConnectionEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                connection_id: ConnectionId::from_str("connection_id").unwrap(),
                height: None
            },
            QueryConnectionEndCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--connection",
                "connection_id"
            ])
        )
    }

    #[test]
    fn test_query_connection_end_conn_alias() {
        assert_eq!(
            QueryConnectionEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                connection_id: ConnectionId::from_str("connection_id").unwrap(),
                height: None
            },
            QueryConnectionEndCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--conn",
                "connection_id"
            ])
        )
    }

    #[test]
    fn test_query_connection_end_height() {
        assert_eq!(
            QueryConnectionEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                connection_id: ConnectionId::from_str("connection_id").unwrap(),
                height: Some(42)
            },
            QueryConnectionEndCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--connection",
                "connection_id",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_connection_end_no_conn() {
        assert!(QueryConnectionEndCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_query_connection_end_no_chain() {
        assert!(
            QueryConnectionEndCmd::try_parse_from(["test", "--connection", "connection_id"])
                .is_err()
        )
    }
}
