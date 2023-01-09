use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryClientConnectionsRequest, QueryClientEventRequest,
    QueryClientStateRequest, QueryConsensusStateHeightsRequest, QueryConsensusStateRequest,
    QueryHeight, QueryTxRequest,
};

use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::events::WithBlockDataType;
use ibc_relayer_types::Height;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};

/// Query client state command
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryClientStateCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client to query"
    )]
    client_id: ClientId,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "The chain height context for the query"
    )]
    height: Option<u64>,
}

/// Command for querying a client's state.
/// hermes query client state --chain ibc-1 --client 07-tendermint-0 --height 3
impl Runnable for QueryClientStateCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        match chain.query_client_state(
            QueryClientStateRequest {
                client_id: self.client_id.clone(),
                height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                    QueryHeight::Specific(
                        Height::new(chain.id().version(), revision_height)
                            .unwrap_or_else(exit_with_unrecoverable_error),
                    )
                }),
            },
            IncludeProof::No,
        ) {
            Ok((cs, _)) => Output::success(cs).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Query client consensus command
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryClientConsensusCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client to query"
    )]
    client_id: ClientId,

    #[clap(
        long = "consensus-height",
        value_name = "CONSENSUS_HEIGHT",
        help = "Height of the client's consensus state to query"
    )]
    consensus_height: Option<u64>,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "The chain height context to be used, applicable only to a specific height"
    )]
    height: Option<u64>,
}

/// Implementation of the query for a client's consensus state at a certain height.
/// hermes query client consensus --chain ibc-0 --client 07-tendermint-0 --consensus-height 22
impl Runnable for QueryClientConsensusCmd {
    fn run(&self) {
        let config = app_config();

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

        if let Some(cs_height) = self.consensus_height {
            let consensus_height = Height::new(counterparty_chain.version(), cs_height)
                .unwrap_or_else(exit_with_unrecoverable_error);

            let res = chain
                .query_consensus_state(
                    QueryConsensusStateRequest {
                        client_id: self.client_id.clone(),
                        consensus_height,
                        query_height: self.height.map_or(QueryHeight::Latest, |revision_height| {
                            QueryHeight::Specific(
                                Height::new(chain.id().version(), revision_height)
                                    .unwrap_or_else(exit_with_unrecoverable_error),
                            )
                        }),
                    },
                    IncludeProof::No,
                )
                .map(|(consensus_state, _)| consensus_state);

            match res {
                Ok(cs) => Output::success(cs).exit(),
                Err(e) => Output::error(e).exit(),
            }
        } else {
            let res = chain.query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                client_id: self.client_id.clone(),
                pagination: Some(PageRequest::all()),
            });

            match res {
                Ok(heights) => Output::success(heights).exit(),
                Err(e) => Output::error(e).exit(),
            }
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryClientHeaderCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client to query"
    )]
    client_id: ClientId,

    #[clap(
        long = "consensus-height",
        required = true,
        value_name = "CONSENSUS_HEIGHT",
        help_heading = "REQUIRED",
        help = "Height of header to query"
    )]
    consensus_height: u64,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "The chain height context for the query. Leave unspecified for latest height."
    )]
    height: Option<u64>,
}

/// Implementation of the query for the header used in a client update at a certain height.
/// hermes query client header --chain ibc-0 --client 07-tendermint-0 --consensus-height 22
impl Runnable for QueryClientHeaderCmd {
    fn run(&self) {
        let config = app_config();

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

        let consensus_height = Height::new(counterparty_chain.version(), self.consensus_height)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let query_height = match self.height {
            Some(revision_height) => QueryHeight::Specific(
                Height::new(chain.id().version(), revision_height)
                    .unwrap_or_else(exit_with_unrecoverable_error),
            ),
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
            Err(e) => Output::error(e).exit(),
        }
    }
}

/// Query client connections command
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct QueryClientConnectionsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_id: ChainId,

    #[clap(
        long = "client",
        required = true,
        value_name = "CLIENT_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client to query"
    )]
    client_id: ClientId,

    #[clap(
        long = "height",
        value_name = "HEIGHT",
        help = "The chain height which this query should reflect"
    )]
    height: Option<u64>,
}

// hermes query connections --chain ibc-0
impl Runnable for QueryClientConnectionsCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = chain.query_client_connections(QueryClientConnectionsRequest {
            client_id: self.client_id.clone(),
        });

        match res {
            Ok(ce) => Output::success(ce).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        QueryClientConnectionsCmd, QueryClientConsensusCmd, QueryClientHeaderCmd,
        QueryClientStateCmd,
    };

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

    #[test]
    fn test_query_client_connections_required_only() {
        assert_eq!(
            QueryClientConnectionsCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                height: None
            },
            QueryClientConnectionsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id"
            ])
        )
    }

    #[test]
    fn test_query_client_connections_height() {
        assert_eq!(
            QueryClientConnectionsCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                height: Some(42)
            },
            QueryClientConnectionsCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_client_connections_no_client() {
        assert!(QueryClientConnectionsCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_query_client_connections_no_chain() {
        assert!(
            QueryClientConnectionsCmd::try_parse_from(["test", "--client", "client_id"]).is_err()
        )
    }

    #[test]
    fn test_query_client_consensus_required_only() {
        assert_eq!(
            QueryClientConsensusCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                consensus_height: None,
                height: None
            },
            QueryClientConsensusCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id"
            ])
        )
    }

    #[test]
    fn test_query_client_consensus_consensus_height() {
        assert_eq!(
            QueryClientConsensusCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                consensus_height: Some(42),
                height: None
            },
            QueryClientConsensusCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--consensus-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_client_consensus_height() {
        assert_eq!(
            QueryClientConsensusCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                consensus_height: None,
                height: Some(42)
            },
            QueryClientConsensusCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_client_consensus_no_client() {
        assert!(QueryClientConsensusCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_query_client_consensus_no_chain() {
        assert!(QueryClientConsensusCmd::try_parse_from(["test", "--client", "client_id"]).is_err())
    }

    #[test]
    fn test_query_client_header_required_only() {
        assert_eq!(
            QueryClientHeaderCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                consensus_height: 42,
                height: None
            },
            QueryClientHeaderCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--consensus-height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_client_header_height() {
        assert_eq!(
            QueryClientHeaderCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                consensus_height: 42,
                height: Some(21)
            },
            QueryClientHeaderCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--consensus-height",
                "42",
                "--height",
                "21"
            ])
        )
    }

    #[test]
    fn test_query_client_header_no_consensus_height() {
        assert!(QueryClientHeaderCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--client",
            "client_id"
        ])
        .is_err())
    }

    #[test]
    fn test_query_client_header_no_client() {
        assert!(QueryClientHeaderCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--consensus-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_query_client_header_no_chain() {
        assert!(QueryClientHeaderCmd::try_parse_from([
            "test",
            "--client",
            "client_id",
            "--consensus-height",
            "42"
        ])
        .is_err())
    }

    #[test]
    fn test_query_client_state_required_only() {
        assert_eq!(
            QueryClientStateCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                height: None
            },
            QueryClientStateCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id"
            ])
        )
    }

    #[test]
    fn test_query_client_state_height() {
        assert_eq!(
            QueryClientStateCmd {
                chain_id: ChainId::from_string("chain_id"),
                client_id: ClientId::from_str("client_id").unwrap(),
                height: Some(42)
            },
            QueryClientStateCmd::parse_from([
                "test",
                "--chain",
                "chain_id",
                "--client",
                "client_id",
                "--height",
                "42"
            ])
        )
    }

    #[test]
    fn test_query_client_state_no_client() {
        assert!(QueryClientStateCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_query_client_state_no_chain() {
        assert!(QueryClientStateCmd::try_parse_from(["test", "--client", "client_id"]).is_err())
    }
}
