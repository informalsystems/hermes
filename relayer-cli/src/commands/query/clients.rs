use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::handle::ChainHandle;
use serde::Serialize;

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::chain::requests::{PageRequest, QueryClientStatesRequest};

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;
use crate::prelude::*;

/// Query clients command
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryAllClientsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(
        short,
        long,
        help = "filter for clients which target a specific chain id (implies '-o')",
        value_name = "ID"
    )]
    src_chain_id: Option<ChainId>,

    #[clap(short, long, help = "omit printing the source chain for each client")]
    omit_chain_ids: bool,
}

#[derive(Debug, Serialize)]
struct ClientChain {
    client_id: ClientId,
    chain_id: ChainId,
}

/// Command for querying all clients.
/// hermes -c cfg.toml query clients ibc-1
impl Runnable for QueryAllClientsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res: Result<_, Error> = chain
            .query_clients(QueryClientStatesRequest {
                pagination: Some(PageRequest::all()),
            })
            .map_err(Error::relayer);

        match res {
            Ok(clients) => {
                match self.src_chain_id.clone() {
                    None => {
                        match self.omit_chain_ids {
                            true => {
                                // Omit chain identifiers
                                debug!(
                                    "printing identifiers of all clients hosted on chain {}",
                                    self.chain_id
                                );
                                let out: Vec<ClientId> =
                                    clients.into_iter().map(|cs| cs.client_id).collect();
                                Output::success(out).exit()
                            }
                            false => {
                                // Include chain identifiers
                                debug!("printing identifiers (and target chain identifiers) of all clients hosted on chain {}", self.chain_id);
                                let out: Vec<ClientChain> = clients
                                    .into_iter()
                                    .map(|cs| ClientChain {
                                        client_id: cs.client_id,
                                        chain_id: cs.client_state.chain_id(),
                                    })
                                    .collect();
                                Output::success(out).exit()
                            }
                        };
                    }
                    Some(source_chain_id) => {
                        debug!(
                            "printing identifiers of all clients hosted on chain {} which target chain {}",
                            self.chain_id, source_chain_id
                        );
                        // Filter and omit chain ids
                        let out: Vec<ClientId> = clients
                            .into_iter()
                            .filter(|cs| cs.client_state.chain_id().eq(&source_chain_id))
                            .map(|cs| cs.client_id)
                            .collect();
                        Output::success(out).exit()
                    }
                }
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
