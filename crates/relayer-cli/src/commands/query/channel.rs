use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::handle::ChainHandle;

use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;
use ibc_relayer_types::core::ics04_channel::channel::State;
use ibc_relayer_types::Height;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryChannelEndCmd {
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
}

impl Runnable for QueryChannelEndCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_channel(
            QueryChannelRequest {
                port_id: self.port_id.clone(),
                channel_id: self.channel_id.clone(),
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
            Ok((channel_end, _)) => {
                if channel_end.state_matches(&State::Uninitialized) {
                    Output::error(format!(
                        "port '{}' & channel '{}' does not exist",
                        self.port_id, self.channel_id
                    ))
                    .exit()
                } else {
                    Output::success(channel_end).exit()
                }
            }
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::QueryChannelEndCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};

    #[test]
    fn test_query_channel_end_required_only() {
        assert_eq!(
            QueryChannelEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: None
            },
            QueryChannelEndCmd::parse_from([
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
    fn test_query_channel_end_chan_alias() {
        assert_eq!(
            QueryChannelEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: None
            },
            QueryChannelEndCmd::parse_from([
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
    fn test_query_channel_end_height() {
        assert_eq!(
            QueryChannelEndCmd {
                chain_id: ChainId::from_string("chain_id"),
                port_id: PortId::from_str("port_id").unwrap(),
                channel_id: ChannelId::from_str("channel-07").unwrap(),
                height: Some(42)
            },
            QueryChannelEndCmd::parse_from([
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
    fn test_query_channel_end_no_chan() {
        assert!(QueryChannelEndCmd::try_parse_from([
            "test", "--chain", "chain_id", "--port", "port_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_channel_end_no_port() {
        assert!(QueryChannelEndCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }

    #[test]
    fn test_query_channel_end_no_chain() {
        assert!(QueryChannelEndCmd::try_parse_from([
            "test",
            "--port",
            "port_id",
            "--channel",
            "channel-07"
        ])
        .is_err())
    }
}
