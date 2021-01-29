use std::sync::Arc;

use abscissa_core::{Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::ChainId;
use ibc_proto::ibc::core::channel::v1::QueryChannelsRequest;
use ibc_relayer::chain::{Chain, CosmosSDKChain};
use ibc_relayer::config::{ChainConfig, Config};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryChannelsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,
}

impl QueryChannelsCmd {
    fn validate_options(&self, config: &Config) -> Result<ChainConfig, String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("missing configuration for chain {}", self.chain_id))?;

        Ok(chain_config.clone())
    }
}

// hermes -c config.toml query channels ibc-0
impl Runnable for QueryChannelsCmd {
    fn run(&self) {
        let config = app_config();

        let chain_config = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", chain_config);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let req = QueryChannelsRequest { pagination: None };

        let res = chain.query_channels(req);

        match res {
            Ok(ce) => Output::success(ce).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
