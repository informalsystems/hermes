use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    HeightQuery, IncludeProof, PageRequest, QueryConnectionChannelsRequest, QueryConnectionRequest,
};

use ibc::core::{
    ics03_connection::connection::State,
    ics24_host::identifier::ConnectionId,
    ics24_host::identifier::{ChainId, PortChannelId},
};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryConnectionEndCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the connection to query")]
    connection_id: ConnectionId,

    #[clap(short = 'H', long, help = "height of the state to query")]
    height: Option<u64>,
}

// cargo run --bin hermes -- query connection end ibc-test connectionidone --height 3
impl Runnable for QueryConnectionEndCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_connection(
            QueryConnectionRequest {
                connection_id: self.connection_id.clone(),
                height: self.height.map_or(HeightQuery::Latest, |revision_height| {
                    HeightQuery::Specific(ibc::Height::new(chain.id().version(), revision_height))
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
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Command for querying the channel identifiers associated with a connection.
/// Sample invocation:
/// `cargo run --bin hermes -- query connection channels ibc-0 connection-0`
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryConnectionChannelsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the connection to query")]
    connection_id: ConnectionId,
}

impl Runnable for QueryConnectionChannelsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

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
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
