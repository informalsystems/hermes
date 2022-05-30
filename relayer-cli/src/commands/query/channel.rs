use alloc::sync::Arc;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::requests::QueryChannelRequest;
use ibc_relayer::chain::{ChainEndpoint, CosmosSdkChain};

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

        let chain_config = match config.find_chain(&self.chain_id) {
            None => Output::error(format!(
                "chain '{}' not found in configuration file",
                self.chain_id
            ))
            .exit(),
            Some(chain_config) => chain_config,
        };

        debug!("Options: {:?}", self);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_channel(QueryChannelRequest {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id,
            height: ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
        });
        match res {
            Ok(channel_end) => {
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
