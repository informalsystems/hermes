use std::sync::Arc;

use abscissa_core::{Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::{ChainId, ChannelId, PortChannelId, PortId};
use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;
use ibc_relayer::chain::{Chain, CosmosSdkChain};

use crate::conclude::Output;
use crate::prelude::*;
use std::str::FromStr;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryChannelsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,
}

// hermes query channels ibc-0
impl Runnable for QueryChannelsCmd {
    fn run(&self) {
        let config = app_config();

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        debug!("Options: {:?}", self);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt).unwrap();

        let req = QueryChannelsRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let res = chain.query_channels(req);

        match res {
            Ok(channels) => {
                let ids: Vec<PortChannelId> = channels
                    .iter()
                    .filter_map(|ch| {
                        let port_id = PortId::from_str(ch.port_id.as_str()).ok();
                        let channel_id = ChannelId::from_str(ch.channel_id.as_str()).ok();
                        match (port_id, channel_id) {
                            (Some(port_id), Some(channel_id)) => Some(PortChannelId {
                                port_id,
                                channel_id,
                            }),
                            (_, _) => None,
                        }
                    })
                    .collect();
                Output::success(ids).exit()
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
