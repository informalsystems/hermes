use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tendermint_proto::Protobuf;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::info;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics03_connection::raw::ConnectionIds as ConnectionIDs;
use ibc::ics24_host::error::ValidationError;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics24_host::Path::{ClientConnections, ClientConsensusState, ClientState};
use ibc_relayer::chain::Chain;
use ibc_relayer::chain::CosmosSDKChain;
use ibc_relayer::config::{ChainConfig, Config};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

/// Query client state command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientStateCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,

    #[options(
        help = "whether proof is required; default: false (no proof)",
        short = "p"
    )]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryClientStateOptions {
    client_id: ClientId,
    height: u64,
    proof: bool,
}

impl QueryClientStateCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryClientStateOptions), String> {
        let (chain_config, client_id) =
            validate_common_options(&self.chain_id, &self.client_id, config)?;

        let opts = QueryClientStateOptions {
            client_id,
            height: self.height.unwrap_or(0_u64),
            proof: self.proof.unwrap_or(false),
        };
        Ok((chain_config, opts))
    }
}

/// Command for querying a client's state.
/// To run with proof:
/// hermes -c cfg.toml query client state ibc-1 07-tendermint-0 --height 3
///
/// Run without proof:
/// hermes -c cfg.toml query client state ibc-1 07-tendermint-0 --height 3 -p false
impl Runnable for QueryClientStateCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();
        let height = ibc::Height::new(chain.id().version(), opts.height);

        let res: Result<AnyClientState, Error> = chain
            .query(ClientState(opts.client_id), height, opts.proof)
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| {
                AnyClientState::decode_vec(&v.value).map_err(|e| Kind::Query.context(e).into())
            });
        match res {
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
    client_id: Option<String>,

    #[options(
        free,
        required,
        help = "epoch of the client's consensus state to query"
    )]
    consensus_epoch: Option<u64>,

    #[options(
        free,
        required,
        help = "height of the client's consensus state to query"
    )]
    consensus_height: Option<u64>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryClientConsensusOptions {
    client_id: ClientId,
    revision_number: u64,
    revision_height: u64,
    height: u64,
    proof: bool,
}

impl QueryClientConsensusCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryClientConsensusOptions), String> {
        let (chain_config, client_id) =
            validate_common_options(&self.chain_id, &self.client_id, config)?;

        match (self.consensus_epoch, self.consensus_height) {
            (Some(revision_number), Some(revision_height)) => {
                let opts = QueryClientConsensusOptions {
                    client_id,
                    revision_number,
                    revision_height,
                    height: self.height.unwrap_or(0_u64),
                    proof: self.proof.unwrap_or(true),
                };
                Ok((chain_config, opts))
            }
            (Some(consensus_epoch), None) => Err("missing client consensus height".to_string()),

            (None, _) => Err("missing client consensus epoch".to_string()),
        }
    }
}

/// Implementation of the query for a client's consensus state at a certain height.
/// Run with proof:
/// hermes -c cfg.toml query client consensus ibc-0 ibconeclient 22
///
/// Run without proof:
/// hermes -c cfg.toml query client consensus ibc-0 ibconeclient 22 -p false
impl Runnable for QueryClientConsensusCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();
        let height = ibc::Height::new(chain.id().version(), opts.height);

        let res: Result<AnyConsensusState, Error> = chain
            .query(
                ClientConsensusState {
                    client_id: opts.client_id,
                    epoch: opts.revision_number,
                    height: opts.revision_height,
                },
                height,
                opts.proof,
            )
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| {
                AnyConsensusState::decode_vec(&v.value).map_err(|e| Kind::Query.context(e).into())
            });

        match res {
            Ok(cs) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

fn validate_common_options(
    chain_id: &ChainId,
    client_id: &Option<String>,
    config: &Config,
) -> Result<(ChainConfig, ClientId), String> {
    let chain_config = config
        .find_chain(&chain_id)
        .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

    let client_id = client_id
        .as_ref()
        .ok_or_else(|| "missing client identifier".to_string())?
        .parse()
        .map_err(|err: ValidationError| err.to_string())?;

    Ok((chain_config.clone(), client_id))
}

/// Query client connections command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientConnectionsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,
}

#[derive(Debug)]
struct QueryClientConnectionsOptions {
    client_id: ClientId,
    height: u64,
}

impl QueryClientConnectionsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryClientConnectionsOptions), String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let client_id = self
            .client_id
            .as_ref()
            .ok_or_else(|| "missing client identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryClientConnectionsOptions {
            client_id,
            height: self.height.unwrap_or(0_u64),
        };
        Ok((chain_config.clone(), opts))
    }
}

/// Command to handle query for client connections
/// To run without proof:
/// relayer -c relayer/tests/config/fixtures/relayer_conf_example.toml query client connections chain_A clientidone -h 4 -p false
impl Runnable for QueryClientConnectionsCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();
        let height = ibc::Height::new(chain.id().version(), opts.height);

        let res: Result<ConnectionIDs, Error> = chain
            .query(ClientConnections(opts.client_id), height, false)
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| {
                ConnectionIDs::decode_vec(&v.value).map_err(|e| Kind::Query.context(e).into())
            });

        match res {
            Ok(cs) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Tests
#[cfg(test)]
mod tests {
    use ibc_relayer::config::parse;

    use crate::commands::query::client::{QueryClientConnectionsCmd, QueryClientStateCmd};

    #[test]
    fn parse_query_state_parameters() {
        let default_params = QueryClientStateCmd {
            chain_id: "ibc-0".to_string().parse().unwrap(),
            client_id: Some("ibconeclient".to_string().parse().unwrap()),
            height: None,
            proof: None,
        };

        struct Test {
            name: String,
            params: QueryClientStateCmd,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryClientStateCmd {
                    chain_id: "notibc0oribc1".to_string().parse().unwrap(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No client id specified".to_string(),
                params: QueryClientStateCmd {
                    client_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, non-alpha".to_string(),
                params: QueryClientStateCmd {
                    client_id: Some("p34".to_string()),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/two_chains.toml"
        );

        let config = parse(path).unwrap();

        for test in tests {
            let res = test.params.validate_options(&config);

            match res {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "validate_options should have failed for test {}",
                        test.name
                    );
                }
                Err(err) => {
                    assert!(
                        !test.want_pass,
                        "validate_options failed for test {}, \nerr {}",
                        test.name, err
                    );
                }
            }
        }
    }

    #[test]
    fn parse_query_client_connections_parameters() {
        let default_params = QueryClientConnectionsCmd {
            chain_id: "ibc-0".to_string().parse().unwrap(),
            client_id: Some("clientidone".to_string().parse().unwrap()),
            height: Some(4),
        };

        struct Test {
            name: String,
            params: QueryClientConnectionsCmd,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Good parameters".to_string(),
                params: default_params.clone(),
                want_pass: true,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryClientConnectionsCmd {
                    chain_id: "notibc0oribc1".to_string().parse().unwrap(),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No client id specified".to_string(),
                params: QueryClientConnectionsCmd {
                    client_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad client id, non-alpha".to_string(),
                params: QueryClientConnectionsCmd {
                    client_id: Some("p34".to_string()),
                    ..default_params
                },
                want_pass: false,
            },
        ]
        .into_iter()
        .collect();

        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/two_chains.toml"
        );

        let config = parse(path).unwrap();

        for test in tests {
            let res = test.params.validate_options(&config);

            match res {
                Ok(_res) => {
                    assert!(
                        test.want_pass,
                        "validate_options should have failed for test {}",
                        test.name
                    );
                }
                Err(err) => {
                    assert!(
                        !test.want_pass,
                        "validate_options failed for test {}, \nerr {}",
                        test.name, err
                    );
                }
            }
        }
    }
}
