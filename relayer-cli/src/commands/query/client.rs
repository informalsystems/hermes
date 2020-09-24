use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};

use crate::error::{Error, Kind};
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics24_host::error::ValidationError;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics24_host::Path::{ClientConnections, ClientConsensusState, ClientState};
use relayer::chain::Chain;
use relayer::chain::CosmosSDKChain;
use tendermint::chain::Id as ChainId;
use tendermint_proto::DomainType;

/// Query client state command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientStateCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
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
            height: match self.height {
                Some(h) => h,
                None => 0 as u64,
            },
            proof: match self.proof {
                Some(proof) => proof,
                None => true,
            },
        };
        Ok((chain_config, opts))
    }
}

/// Command for handling a query for a client's state.
/// To run with proof:
/// cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query client state ibc-test ethbridge --height 3
///
/// Run without proof:
/// cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query client state ibc-test ethbridge --height 3 -p false
impl Runnable for QueryClientStateCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        let chain = CosmosSDKChain::from_config(chain_config).unwrap();

        let res: Result<AnyClientState, Error> = chain
            .abci_query(ClientState(opts.client_id), opts.height, opts.proof)
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| {
                AnyClientState::decode_vec(&v).map_err(|e| Kind::Query.context(e).into())
            });
        match res {
            Ok(cs) => status_info!("client state query result: ", "{:?}", cs),
            Err(e) => status_info!("client state query error: ", "{:?}", e),
        }
    }
}

/// Query client consensus command
#[derive(Clone, Command, Debug, Options)]
pub struct QueryClientConsensusCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(free, help = "height of the client's consensus state to query")]
    consensus_height: Option<u64>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryClientConsensusOptions {
    client_id: ClientId,
    consensus_height: u64,
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

        match self.consensus_height {
            Some(consensus_height) => {
                let opts = QueryClientConsensusOptions {
                    client_id,
                    consensus_height,
                    height: match self.height {
                        Some(h) => h,
                        None => 0 as u64,
                    },
                    proof: match self.proof {
                        Some(proof) => proof,
                        None => true,
                    },
                };
                Ok((chain_config, opts))
            }
            None => Err("missing client consensus height".to_string()),
        }
    }
}

/// Implementation of the query for a client's consensus state at a certain height.
/// Run with proof:
/// cargo run --bin relayer -- -c simple_config.toml query client consensus ibc0 ibconeclient 22
///
/// Run without proof:
/// cargo run --bin relayer -- -c simple_config.toml query client consensus ibc0 ibconeclient 22 -p false
impl Runnable for QueryClientConsensusCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        let chain = CosmosSDKChain::from_config(chain_config).unwrap();
        let res: Result<AnyConsensusState, Error> = chain
            .abci_query(
                ClientConsensusState(opts.client_id, opts.consensus_height),
                opts.height,
                opts.proof,
            )
            .map_err(|e| Kind::Query.context(e).into())
            .and_then(|v| {
                AnyConsensusState::decode_vec(&v).map_err(|e| Kind::Query.context(e).into())
            });

        match res {
            Ok(cs) => status_info!("client consensus state query result: ", "{:?}", cs),
            Err(e) => status_info!("client consensus state query error: ", "{:?}", e),
        }
    }
}

fn validate_common_options(
    chain_id: &Option<ChainId>,
    client_id: &Option<String>,
    config: &Config,
) -> Result<(ChainConfig, ClientId), String> {
    let chain_id = chain_id.ok_or_else(|| "missing chain parameter".to_string())?;
    let chain_config = config
        .chains
        .iter()
        .find(|c| c.id == chain_id)
        .ok_or_else(|| "missing chain in configuration".to_string())?;

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
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(help = "the chain height which this query should reflect", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryClientConnectionsOptions {
    client_id: ClientId,
    height: u64,
    proof: bool,
}

impl QueryClientConnectionsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryClientConnectionsOptions), String> {
        let chain_id = self
            .chain_id
            .ok_or_else(|| "missing chain identifier".to_string())?;
        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == chain_id)
            .ok_or_else(|| "missing chain configuration".to_string())?;

        let client_id = self
            .client_id
            .as_ref()
            .ok_or_else(|| "missing client identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryClientConnectionsOptions {
            client_id,
            height: match self.height {
                Some(h) => h,
                None => 0 as u64,
            },
            proof: match self.proof {
                Some(proof) => proof,
                None => true,
            },
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
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        let chain = CosmosSDKChain::from_config(chain_config).unwrap();
        let res = chain.query::<Vec<ConnectionId>>(
            ClientConnections(opts.client_id),
            opts.height,
            opts.proof,
        );
        match res {
            Ok(cs) => status_info!("client connections query result: ", "{:?}", cs),
            Err(e) => status_info!("client connections query error", "{}", e),
        }
    }
}

/// Tests
#[cfg(test)]
mod tests {
    use crate::commands::query::client::{QueryClientConnectionsCmd, QueryClientStateCmd};
    use relayer::config::parse;

    #[test]
    fn parse_query_state_parameters() {
        let default_params = QueryClientStateCmd {
            chain_id: Some("ibc0".to_string().parse().unwrap()),
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
                name: "No chain specified".to_string(),
                params: QueryClientStateCmd {
                    chain_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryClientStateCmd {
                    chain_id: Some("notibc0oribc1".to_string().parse().unwrap()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No client id specified".to_string(),
                params: QueryClientStateCmd {
                    client_id: None,
                    ..default_params
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
            chain_id: Some("ibc0".to_string().parse().unwrap()),
            client_id: Some("clientidone".to_string().parse().unwrap()),
            height: Some(4),
            proof: Some(false),
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
                name: "No chain specified".to_string(),
                params: QueryClientConnectionsCmd {
                    chain_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryClientConnectionsCmd {
                    chain_id: Some("notibc0oribc1".to_string().parse().unwrap()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No client id specified".to_string(),
                params: QueryClientConnectionsCmd {
                    client_id: None,
                    ..default_params
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
