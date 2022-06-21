use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use tracing::debug;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryClientConnectionsRequest, QueryClientEventRequest,
    QueryClientStateRequest, QueryConsensusStateRequest, QueryConsensusStatesRequest, QueryHeight,
    QueryTxRequest,
};

use ibc::core::ics02_client::client_state::ClientState;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::events::WithBlockDataType;
use ibc::Height;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
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

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        match chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.client_id.clone(),
                height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                    QueryHeight::Specific(ibc::Height::new(chain.id().version(), revision_height))
                }),
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => Output::success(cs).exit(),
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

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let counterparty_chain = match chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => cs.chain_id(),
            Err(e) => Output::error(format!(
                "failed while querying client '{}' on chain '{}' with error: {}",
                self.client_id, self.chain_id, e
            ))
            .exit(),
        };

        match self.consensus_height {
            Some(cs_height) => {
                let consensus_height = ibc::Height::new(counterparty_chain.version(), cs_height);

                let res = chain
                    .query_consensus_state(
                        QueryConsensusStateRequest {
                            client_id: self.client_id.clone(),
                            consensus_height,
                            query_height: self.height.map_or(
                                QueryHeight::Latest,
                                |revision_height| {
                                    QueryHeight::Specific(ibc::Height::new(
                                        chain.id().version(),
                                        revision_height,
                                    ))
                                },
                            ),
                        },
                        IncludeProof::No,
                    )
                    .map(|(consensus_state, _)| consensus_state);

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

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let counterparty_chain = match chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => cs.chain_id(),
            Err(e) => Output::error(format!(
                "failed while querying client '{}' on chain '{}' with error: {}",
                self.client_id, self.chain_id, e
            ))
            .exit(),
        };

        let consensus_height =
            ibc::Height::new(counterparty_chain.version(), self.consensus_height);

        let query_height = match self.height {
            Some(revision_height) => {
                QueryHeight::Specific(Height::new(chain.id().version(), revision_height))
            }
            None => QueryHeight::Latest,
        };

        let res = chain.query_txs(QueryTxRequest::Client(QueryClientEventRequest {
            query_height,
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

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)
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
