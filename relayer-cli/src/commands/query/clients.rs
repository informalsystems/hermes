use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::ChainId;
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_relayer::chain::{Chain, CosmosSDKChain};
use ibc_relayer::config::{ChainConfig, Config};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

/// Query clients command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryAllClientsCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: ChainId,
}

impl QueryAllClientsCmd {
    fn validate_options(&self, config: &Config) -> Result<ChainConfig, String> {
        let chain_id = self.chain_id.clone();

        let chain_config = config
            .find_chain(&chain_id)
            .ok_or_else(|| "missing chain configuration for the given chain id".to_string())?;

        Ok(chain_config.clone())
    }
}

/// Command for querying all clients.
/// rrly -c cfg.toml query clients ibc-1  
impl Runnable for QueryAllClientsCmd {
    fn run(&self) {
        let config = app_config();

        let chain_config = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let req = QueryClientStatesRequest { pagination: None };

        let res: Result<_, Error> = chain
            .query_clients(req)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(cids) => Output::success(cids).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
