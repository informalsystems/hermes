use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use relayer::query::connection::query_connection;

use crate::commands::utils::block_on;
use relayer::chain::tendermint::TendermintChain;
use relayer_modules::ics24_host::error::ValidationError;
use relayer_modules::ics24_host::identifier::ConnectionId;
use tendermint::chain::Id as ChainId;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryConnectionEndCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the connection to query")]
    connection_id: Option<String>,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,

    #[options(help = "whether proof is required", short = "p")]
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
            .ok_or_else(|| "missing chain identifier".to_string())?;
        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == chain_id)
            .ok_or_else(|| "missing chain configuration".to_string())?;

        let connection_id = self
            .connection_id
            .as_ref()
            .ok_or_else(|| "missing connection identifier".to_string())?
            .parse()
            .map_err(|err: ValidationError| err.to_string())?;

        let opts = QueryConnectionOptions {
            connection_id,
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

impl Runnable for QueryConnectionEndCmd {
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

        // run with proof:
        // cargo run --bin relayer -- -c simple_config.toml query connection end ibc0 ibconeconnection
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query connection end ibc0 ibconeconnection -p false
        //
        // Note: currently both fail in amino_unmarshal_binary_length_prefixed().
        // To test this start a Gaia node and configure a client using the go relayer.
        let chain = TendermintChain::from_config(chain_config).unwrap();
        let res = block_on(query_connection(
            &chain,
            opts.height,
            opts.connection_id.clone(),
            opts.proof,
        ));
        match res {
            Ok(cs) => status_info!("connection query result: ", "{:?}", cs.connection),
            Err(e) => status_info!("connection query error: ", "{:?}", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::commands::query::connection::QueryConnectionEndCmd;
    use relayer::config::parse;

    #[test]
    fn parse_connection_query_end_parameters() {
        let default_params = QueryConnectionEndCmd {
            chain_id: Some("ibc0".to_string().parse().unwrap()),
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
                    ..default_params.clone()
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
