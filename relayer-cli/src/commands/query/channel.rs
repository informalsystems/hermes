use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::handle::ChainHandle;

use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::prelude::*;
use ibc::core::ics04_channel::channel::State;

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryChannelEndCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the port to query")]
    port_id: PortId,

    #[clap(required = true, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[clap(short = 'H', long, help = "height of the state to query")]
    height: Option<u64>,
}

impl Runnable for QueryChannelEndCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_channel(
            QueryChannelRequest {
                port_id: self.port_id.clone(),
                channel_id: self.channel_id,
                height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                    QueryHeight::Specific(ibc::Height::new(chain.id().version(), revision_height))
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
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
