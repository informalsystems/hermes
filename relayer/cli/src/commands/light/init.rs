use std::future::Future;

// use crate::application::APPLICATION;
use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::lite::Height;

use relayer::chain::tendermint::TendermintChain;
use relayer::client::trust_options::TrustOptions;
use relayer::config::{ChainConfig, Config};
use relayer::store::{sled::SledStore, Store};

#[derive(Command, Debug, Options)]
pub struct InitCmd {
    #[options(free, help = "identifier of the chain to initialize light client for")]
    chain_id: Option<ChainId>,

    #[options(help = "trusted header hash", short = "x")]
    hash: Option<Hash>,

    #[options(help = "trusted header height", short = "h")]
    height: Option<Height>,
}

#[derive(Clone, Debug)]
struct InitOptions {
    /// identifier of chain to initialize light client for
    chain_id: ChainId,

    /// trusted header hash
    trusted_hash: Hash,

    /// trusted header height
    trusted_height: Height,
}

impl InitCmd {
    fn get_chain_config_and_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, InitOptions), String> {
        match (&self.chain_id, &self.hash, self.height) {
            (Some(chain_id), Some(trusted_hash), Some(trusted_height)) => {
                let chain_config = config.chains.iter().find(|c| c.id == *chain_id);

                match chain_config {
                    Some(chain_config) => {
                        let opts = InitOptions {
                            chain_id: *chain_id,
                            trusted_hash: *trusted_hash,
                            trusted_height,
                        };

                        Ok((chain_config.clone(), opts))
                    }
                    None => Err(format!("cannot find chain {} in config", chain_id)),
                }
            }

            (None, _, _) => Err("missing chain identifier".to_string()),
            (_, None, _) => Err("missing trusted hash".to_string()),
            (_, _, None) => Err("missing trusted height".to_string()),
        }
    }
}

impl Runnable for InitCmd {
    /// Initialize the light client for the given chain
    fn run(&self) {
        // FIXME: This just hangs and never runs the given future
        // abscissa_tokio::run(&APPLICATION, ...).unwrap();

        let config = app_config();

        let (chain_config, opts) = match self.get_chain_config_and_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };

        block_on(async {
            let trust_options = TrustOptions::new(
                opts.trusted_hash,
                opts.trusted_height,
                chain_config.trusting_period,
                Default::default(),
            )
            .unwrap();

            let mut store: SledStore<TendermintChain> =
                relayer::store::persistent(format!("store_{}.db", chain_config.id));

            store.set_trust_options(trust_options).unwrap(); // FIXME: unwrap

            status_ok!(
                chain_config.id,
                "Set trusted options: hash={} height={}",
                opts.trusted_hash,
                opts.trusted_height
            );
        });
    }
}

fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
