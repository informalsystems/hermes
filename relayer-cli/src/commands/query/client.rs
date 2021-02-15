use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;
use tracing::info;

use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::ClientId;
use ibc_proto::ibc::core::connection::v1::QueryClientConnectionsRequest;
use ibc_relayer::chain::Chain;
use ibc_relayer::chain::CosmosSDKChain;

use crate::conclude::Output;
use crate::prelude::*;

/// Query client state command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientStateCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to query")]
    client_id: ClientId,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,
}

/// Command for querying a client's state.
/// hermes query client state ibc-1 07-tendermint-0 --height 3
impl Runnable for QueryClientStateCmd {
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

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config.clone(), rt).unwrap();
        let height = ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64));

        match chain.query_client_state(&self.client_id, height) {
            Ok(cs) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Query client consensus command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientConsensusCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to query")]
    client_id: ClientId,

    #[options(
        free,
        required,
        help = "revision number of the client's consensus state to query"
    )]
    consensus_rev_number: u64,

    #[options(
        free,
        required,
        help = "height (revision height) of the client's consensus state to query"
    )]
    consensus_rev_height: u64,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,
}

/// Implementation of the query for a client's consensus state at a certain height.
/// hermes query client consensus ibc-0 07-tendermint-0 22
impl Runnable for QueryClientConsensusCmd {
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

        info!("Options {:?}", self);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config.clone(), rt).unwrap();
        let consensus_height = ibc::Height::new(self.consensus_rev_number, self.consensus_rev_height);
        let height = ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64));

        match chain.proven_client_consensus(&self.client_id, consensus_height, height) {
            Ok((cs, _)) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Query client connections command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientConnectionsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to query")]
    client_id: ClientId,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,
}

// hermes query connections ibc-0
impl Runnable for QueryClientConnectionsCmd {
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

        info!("Options {:?}", self);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config.clone(), rt).unwrap();

        let req = QueryClientConnectionsRequest {
            client_id: self.client_id.to_string(),
        };

        let res = chain.query_client_connections(req);

        match res {
            Ok(ce) => Output::success(ce).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
