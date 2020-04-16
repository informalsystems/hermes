use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::{ChainConfig, Config};
use relayer::query::client::{query_client_consensus_state, query_client_full_state};

use relayer_modules::ics24_host::client::ClientId;

use crate::commands::utils::block_on;
use relayer::chain::tendermint::TendermintChain;
use tendermint::chain::Id as ChainId;

#[derive(Command, Debug, Options)]
pub struct QueryClientStateCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(help = "height of the state to query", short = "h")]
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
            client_id: client_id.parse().unwrap(),
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

        // run with proof:
        // cargo run --bin relayer -- -c simple_config.toml query client state ibc0 ibconeclient
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query client state ibc0 ibconeclient -p false
        //
        // Note: currently both fail in amino_unmarshal_binary_length_prefixed().
        // To test this start a Gaia node and configure a client using the go relayer.
        let chain = TendermintChain::from_config(chain_config).unwrap();
        let res = block_on(query_client_full_state(
            &chain,
            opts.height,
            opts.client_id.clone(),
            opts.proof,
        ));
        match res {
            Ok(cs) => status_info!("client state query result: ", "{:?}", cs.client_state),
            Err(e) => status_info!("client state query error: ", "{:?}", e),
        }
    }
}

#[derive(Command, Debug, Options)]
pub struct QueryClientConsensusCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: Option<ChainId>,

    #[options(free, help = "identifier of the client to query")]
    client_id: Option<String>,

    #[options(free, help = "height of the consensus state to query")]
    consensus_height: Option<u64>,

    #[options(help = "height of the consensus state to query", short = "h")]
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
                    client_id: client_id.parse().unwrap(),
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
                Ok((chain_config.clone(), opts))
            }
            None => Err("missing client consensus height".to_string()),
        }
    }
}

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

        // run with proof:
        // cargo run --bin relayer -- -c simple_config.toml query client consensus ibc0 ibconeclient 22
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query client consensus ibc0 ibconeclient 22 -p false
        //
        // Note: currently both fail in amino_unmarshal_binary_length_prefixed().
        // To test this start a Gaia node and configure a client using the go relayer.
        let chain = TendermintChain::from_config(chain_config).unwrap();
        let res = block_on(query_client_consensus_state(
            &chain,
            opts.height,
            opts.client_id,
            opts.consensus_height,
            opts.proof,
        ));
        match res {
            Ok(cs) => status_info!(
                "client consensus state query result: ",
                "{:?}",
                cs.consensus_state
            ),
            Err(e) => status_info!("client consensus state query error: ", "{:?}", e),
        }
    }
}

fn validate_common_options(
    chain_id: &Option<ChainId>,
    client_id: &Option<String>,
    config: &Config,
) -> Result<(ChainConfig, String), String> {
    match (&chain_id, &client_id) {
        (Some(chain_id), Some(client_id)) => {
            let chain_config = config.chains.iter().find(|c| c.id == *chain_id);

            match chain_config {
                Some(chain_config) => {
                    // check that the client_id is specified in one of the chain configurations
                    match config
                        .chains
                        .iter()
                        .find(|c| c.client_ids.contains(client_id))
                    {
                        Some(_) => Ok((chain_config.clone(), client_id.parse().unwrap())),
                        None => Err(format!("cannot find client {} in config", client_id)),
                    }
                }
                None => Err(format!("cannot find chain {} in config", chain_id)),
            }
        }

        (None, _) => Err("missing chain identifier".to_string()),
        (_, None) => Err("missing client identifier".to_string()),
    }
}
