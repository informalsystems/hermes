use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics24_host::error::ValidationError;
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::ConnectionId;
use ibc_proto::ibc::core::channel::v1::QueryConnectionChannelsRequest;
use ibc_relayer::chain::{Chain, CosmosSDKChain};
use ibc_relayer::config::{ChainConfig, Config};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryConnectionEndCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, required, help = "identifier of the connection to query")]
    connection_id: Option<String>,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,

    #[options(
        help = "whether proof is required; default: false (no proof)",
        short = "p"
    )]
    proof: Option<bool>,
}

#[derive(Debug)]
struct QueryConnectionOptions {
    connection_id: ConnectionId,
    height: u64,
    proof: bool,
}

impl QueryConnectionEndCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryConnectionOptions), String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "missing chain identifier".to_string())?;

        let chain_config = config
            .find_chain(&chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

        let connection_id = self
            .connection_id
            .as_ref()
            .ok_or_else(|| "missing connection identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryConnectionOptions {
            connection_id,
            height: self.height.unwrap_or(0_u64),
            proof: self.proof.unwrap_or(true),
        };
        Ok((chain_config.clone(), opts))
    }
}

// cargo run --bin hermes -- -c relayer/tests/config/fixtures/simple_config.toml query connection end ibc-test connectionidone --height 3
impl Runnable for QueryConnectionEndCmd {
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

        // TODO - any value in querying with proof from the CLI?
        let res: Result<ConnectionEnd, Error> = chain
            .query_connection(&opts.connection_id, height)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(ce) => Output::success(ce).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// Command for querying the channel identifiers associated with a connection.
/// Sample invocation:
/// `cargo run --bin hermes -- -c simple_config.toml query connection channels ibc-0 connection-0`
#[derive(Clone, Command, Debug, Options)]
pub struct QueryConnectionChannelsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, required, help = "identifier of the connection to query")]
    connection_id: Option<String>,
}

#[derive(Debug)]
struct QueryConnectionChannelsOptions {
    connection_id: ConnectionId,
}

impl QueryConnectionChannelsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryConnectionChannelsOptions), String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "no chain chain identifier provided".to_string())?;
        let chain_config = config
            .find_chain(&chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

        let connection_id = self
            .connection_id
            .as_ref()
            .ok_or_else(|| "no connection identifier was provided".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryConnectionChannelsOptions { connection_id };

        Ok((chain_config.clone(), opts))
    }
}

impl Runnable for QueryConnectionChannelsCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let req = QueryConnectionChannelsRequest {
            connection: opts.connection_id.to_string(),
            pagination: None,
        };

        let res: Result<_, Error> = chain
            .query_connection_channels(req)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(cids) => Output::success(cids).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[cfg(test)]
mod tests {
    use ibc_relayer::config::parse;

    use crate::commands::query::connection::{QueryConnectionChannelsCmd, QueryConnectionEndCmd};

    #[test]
    fn parse_connection_query_end_parameters() {
        let default_params = QueryConnectionEndCmd {
            chain_id: Some("ibc-0".to_string().parse().unwrap()),
            connection_id: Some("ibconeconnection".to_string().parse().unwrap()),
            height: None,
            proof: None,
        };

        struct Test {
            name: String,
            params: QueryConnectionEndCmd,
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
                params: QueryConnectionEndCmd {
                    chain_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryConnectionEndCmd {
                    chain_id: Some("notibc0oribc1".to_string().parse().unwrap()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No connection id specified".to_string(),
                params: QueryConnectionEndCmd {
                    connection_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection, non-alpha".to_string(),
                params: QueryConnectionEndCmd {
                    connection_id: Some("conn01".to_string()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection, name too short".to_string(),
                params: QueryConnectionEndCmd {
                    connection_id: Some("connshort".to_string()),
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
    fn parse_query_connection_channels_parameters() {
        let default_params = QueryConnectionChannelsCmd {
            chain_id: Some("ibc-0".to_string().parse().unwrap()),
            connection_id: Some("ibconeconnection".to_string().parse().unwrap()),
        };

        struct Test {
            name: String,
            params: QueryConnectionChannelsCmd,
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
                params: QueryConnectionChannelsCmd {
                    chain_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Chain not configured".to_string(),
                params: QueryConnectionChannelsCmd {
                    chain_id: Some("ibc007".to_string().parse().unwrap()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "No connection id specified".to_string(),
                params: QueryConnectionChannelsCmd {
                    connection_id: None,
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection, non-alpha".to_string(),
                params: QueryConnectionChannelsCmd {
                    connection_id: Some("connection-0^".to_string()),
                    ..default_params.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Bad connection, name too short".to_string(),
                params: QueryConnectionChannelsCmd {
                    connection_id: Some("connshort".to_string()),
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
