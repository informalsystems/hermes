use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use relayer::query::connection::query_connection;

use crate::commands::utils::block_on;
use relayer::chain::tendermint::TendermintChain;
use relayer_modules::ics24_host::identifier::ConnectionId;
use tendermint::chain::Id as ChainId;

#[derive(Command, Debug, Options)]
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
        let (chain_config, connection_id) =
            validate_common_options(&self.chain_id, &self.connection_id, config)?;
        let opts = QueryConnectionOptions {
            connection_id: connection_id.parse().unwrap(),
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

fn validate_common_options(
    chain_id: &Option<ChainId>,
    connection_id: &Option<String>,
    config: &Config,
) -> Result<(ChainConfig, String), String> {
    match (&chain_id, &connection_id) {
        (Some(chain_id), Some(connection_id)) => {
                let chain_config = config.chains.iter().find(|c| c.id == *chain_id);

                match chain_config {
                    Some(chain_config) => {
                        // Check for valid connection id for the given chain_id
                        // config.connections.as_ref()
                        //         .unwrap()
                        //         .iter()
                        //         .find(|conn|
                        //             conn.dest.as_ref().unwrap().connection_id.as_ref().unwrap() == connection_id && chain_config.client_ids.contains(&conn.dest.as_ref().unwrap().client_id));


                        Ok((chain_config.clone(), connection_id.parse().unwrap()))

                    // _ => Err(format!("cannot find connection {} for chain {} in config", connection_id, chain_id)),

                }
                    None => Err(format!("cannot find chain {} in config", chain_id)),
            }
        }

        (None, _) => Err("missing chain identifier".to_string()),
        (_, None) => Err("missing connection identifier".to_string()),
    }
}
