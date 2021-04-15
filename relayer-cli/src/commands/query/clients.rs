use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics24_host::identifier::ChainId;
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_relayer::chain::{Chain, CosmosSdkChain};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

/// Query clients command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryAllClientsCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: ChainId,
}

/// Command for querying all clients.
/// hermes -c cfg.toml query clients ibc-1  
impl Runnable for QueryAllClientsCmd {
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

        let req = QueryClientStatesRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let res: Result<_, Error> = chain
            .query_clients(req)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(cids) => Output::success(cids).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
