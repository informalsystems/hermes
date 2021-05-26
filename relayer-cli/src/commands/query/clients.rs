use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;
use serde::Serialize;

use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_relayer::chain::{Chain, CosmosSdkChain};


use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

/// Query clients command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryAllClientsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(help = "filter for clients which target a specific chain id", long = "src-chain-id",
    short = "s", meta = "ID")]
    filter: Option<ChainId>,

    #[options(
        help = "omit printing the chain identifier which each client targets; \
                providing a `-s`/`--src-chain-id` will enable this option",
        default = "false"
    )]
    omit_chain_ids: bool,
}

#[derive(Debug, Serialize)]
struct ChainClientTuple {
    client_id: ClientId,
    target_chain_id: String,
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
            Ok(clients) => {
                match self.filter.clone() {
                    None => {
                        match self.omit_chain_ids {
                            true => {
                                // Omit chain identifiers
                                info!("printing identifiers of all clients hosted on chain {}", self.chain_id);
                                let out: Vec<ClientId> =
                                    clients.into_iter().map(|cs| cs.client_id).collect();
                                Output::success(out).exit()
                            }
                            false => {
                                // Include chain identifiers
                                info!("printing identifiers (and target chain identifiers) of all clients hosted on chain {}", self.chain_id);
                                let out: Vec<ChainClientTuple> = clients
                                    .into_iter()
                                    .map(|cs| ChainClientTuple { client_id: cs.client_id, target_chain_id: cs.client_state.chain_id().to_string() } )
                                    .collect();
                                Output::success(out).exit()
                            }
                        };
                    }
                    Some(source_chain_id) => {
                        info!("filtering for client hosted on chain {} which target chain {}", self.chain_id, source_chain_id);
                        // Filter and omit chain ids
                        let out: Vec<ClientId> =
                            clients.into_iter()
                                .filter(|cs| cs.client_state.chain_id().eq(&source_chain_id))
                                .map(|cs| cs.client_id).collect();
                        Output::success(out).exit()
                    }
                }
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
