use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use core::future::Future;
use relayer::config::{ChainConfig, Config};
use relayer::query::client_consensus_state::query_client_consensus_state;
use relayer::query::client_state::query_client_latest_state;
use relayer_modules::ics24_host::client::ClientId;
use tokio::runtime::Builder;

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
        match (&self.chain_id, &self.client_id) {
            (Some(chain_id), Some(client_id)) => {
                let chain_config = config.chains.iter().find(|c| c.id == *chain_id);

                match chain_config {
                    Some(chain_config) => {
                        // check that the client_id is specified in one of the chain configurations
                        match config
                            .chains
                            .iter()
                            .find(|c| c.client_ids.contains(&client_id))
                        {
                            Some(_) => {
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
        // this causes earlier error in ibc_query(): `.map_err(|e| error::Kind::Rpc.context(e))?;:`
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query client state ibc0 ibconeclient -p false
        // this one fails in amino_unmarshal_binary_length_prefixed() as expected
        //
        let chain = TendermintChain::from_config(chain_config).unwrap();
        // To test this start a Gaia node and configure a client with the go relayer.
        let _res = block_on(query_client_latest_state(
            &chain,
            opts.height,
            opts.client_id.clone(),
            opts.proof,
        ))
        .unwrap();
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
        match (&self.chain_id, &self.client_id, self.consensus_height) {
            (Some(chain_id), Some(client_id), Some(consensus_height)) => {
                let chain_config = config.chains.iter().find(|c| c.id == *chain_id);

                match chain_config {
                    Some(chain_config) => {
                        // check that the client_id is specified in one of the chain configurations
                        match config
                            .chains
                            .iter()
                            .find(|c| c.client_ids.contains(&client_id))
                        {
                            Some(_) => {
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
                            None => Err(format!("cannot find client {} in config", client_id)),
                        }
                    }
                    None => Err(format!("cannot find chain {} in config", chain_id)),
                }
            }

            (None, _, _) => Err("missing chain identifier".to_string()),
            (_, None, _) => Err("missing client identifier".to_string()),
            (_, _, None) => Err("missing client consensus height".to_string()),
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
        // this causes earlier error in ibc_query(): `.map_err(|e| error::Kind::Rpc.context(e))?;:`
        //
        // run without proof:
        // cargo run --bin relayer -- -c simple_config.toml query client consensus ibc0 ibconeclient 22 -p false
        // this one fails in amino_unmarshal_binary_length_prefixed() as expected
        //
        let chain = TendermintChain::from_config(chain_config).unwrap();
        let _res = block_on(query_client_consensus_state(
            &chain,
            opts.height,
            opts.client_id,
            opts.consensus_height,
            opts.proof,
        ))
        .unwrap();
    }
}

fn block_on<F: Future>(future: F) -> F::Output {
    Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
