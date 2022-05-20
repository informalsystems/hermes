use alloc::sync::Arc;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::requests::{
    PageRequest, QueryClientConnectionsRequest, QueryClientStateRequest,
    QueryConsensusStateRequest, QueryConsensusStatesRequest,
};
use tokio::runtime::Runtime as TokioRuntime;
use tracing::debug;

use ibc::core::ics02_client::client_consensus::QueryClientEventRequest;
use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::events::WithBlockDataType;
use ibc::query::QueryTxRequest;
use ibc::Height;
use ibc_relayer::chain::ChainEndpoint;
use ibc_relayer::chain::CosmosSdkChain;

use crate::application::app_config;
use crate::conclude::{exit_with_unrecoverable_error, Output};

/// Query client state command
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryClientStateCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the client to query")]
    client_id: ClientId,

    #[clap(short = 'H', long, help = "the chain height context for the query")]
    height: Option<u64>,
}

/// Command for querying a client's state.
/// hermes query client state ibc-1 07-tendermint-0 --height 3
impl Runnable for QueryClientStateCmd {
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

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSdkChain::bootstrap(chain_config.clone(), rt)
            .unwrap_or_else(exit_with_unrecoverable_error);
        let height = ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64));

        match chain.query_client_state(QueryClientStateRequest {
            client_id: self.client_id.clone(),
            height,
        }) {
            Ok(cs) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Query client consensus command
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryClientConsensusCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the client to query")]
    client_id: ClientId,

    #[clap(
        short = 'c',
        long,
        help = "height of the client's consensus state to query"
    )]
    consensus_height: Option<u64>,

    #[clap(short = 's', long, help = "show only consensus heights")]
    heights_only: bool,

    #[clap(
        short = 'H',
        long,
        help = "the chain height context to be used, applicable only to a specific height"
    )]
    height: Option<u64>,
}

/// Implementation of the query for a client's consensus state at a certain height.
/// hermes query client consensus ibc-0 07-tendermint-0 -c 22
impl Runnable for QueryClientConsensusCmd {
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

        let counterparty_chain = match chain.query_client_state(QueryClientStateRequest {
            client_id: self.client_id.clone(),
            height: Height::zero(),
        }) {
            Ok(cs) => cs.chain_id(),
            Err(e) => Output::error(format!(
                "failed while querying client '{}' on chain '{}' with error: {}",
                self.client_id, self.chain_id, e
            ))
            .exit(),
        };

        match self.consensus_height {
            Some(cs_height) => {
                let height = ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64));
                let consensus_height = ibc::Height::new(counterparty_chain.version(), cs_height);

                let res = chain.query_consensus_state(QueryConsensusStateRequest {
                    client_id: self.client_id.clone(),
                    consensus_height,
                    query_height: height,
                });

                match res {
                    Ok(cs) => Output::success(cs).exit(),
                    Err(e) => Output::error(format!("{}", e)).exit(),
                }
            }
            None => {
                let res = chain.query_consensus_states(QueryConsensusStatesRequest {
                    client_id: self.client_id.clone(),
                    pagination: Some(PageRequest::all()),
                });

                match res {
                    Ok(states) => {
                        if self.heights_only {
                            let heights: Vec<Height> = states.iter().map(|cs| cs.height).collect();
                            Output::success(heights).exit()
                        } else {
                            Output::success(states).exit()
                        }
                    }
                    Err(e) => Output::error(format!("{}", e)).exit(),
                }
            }
        }
    }
}

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryClientHeaderCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the client to query")]
    client_id: ClientId,

    #[clap(required = true, help = "height of header to query")]
    consensus_height: u64,

    #[clap(short = 'H', long, help = "the chain height context for the query")]
    height: Option<u64>,
}

/// Implementation of the query for the header used in a client update at a certain height.
/// hermes query client header ibc-0 07-tendermint-0 22
impl Runnable for QueryClientHeaderCmd {
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

        let counterparty_chain = match chain.query_client_state(QueryClientStateRequest {
            client_id: self.client_id.clone(),
            height: Height::zero(),
        }) {
            Ok(cs) => cs.chain_id(),
            Err(e) => Output::error(format!(
                "failed while querying client '{}' on chain '{}' with error: {}",
                self.client_id, self.chain_id, e
            ))
            .exit(),
        };

        let consensus_height =
            ibc::Height::new(counterparty_chain.version(), self.consensus_height);
        let height = ibc::Height::new(chain.id().version(), self.height.unwrap_or(0_u64));

        let res = chain.query_txs(QueryTxRequest::Client(QueryClientEventRequest {
            height,
            event_id: WithBlockDataType::UpdateClient,
            client_id: self.client_id.clone(),
            consensus_height,
        }));

        match res {
            Ok(header) => Output::success(header).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Query client connections command
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryClientConnectionsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the client to query")]
    client_id: ClientId,

    #[clap(
        short = 'H',
        long,
        help = "the chain height which this query should reflect"
    )]
    height: Option<u64>,
}

// hermes query connections ibc-0
impl Runnable for QueryClientConnectionsCmd {
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

        let res = chain.query_client_connections(QueryClientConnectionsRequest {
            client_id: self.client_id.clone(),
        });

        match res {
            Ok(ce) => Output::success(ce).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
