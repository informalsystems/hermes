use std::future::Future;

use crate::light::config::{LightConfig, LIGHT_CONFIG_PATH};
use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint_light_client::types::TrustThreshold;

use relayer::chain::CosmosSDKChain;
use relayer::client::trust_options::TrustOptions;
use relayer::config::{ChainConfig, Config};

#[derive(Command, Debug, Options)]
pub struct InitCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<ChainId>,

    #[options(help = "trusted header hash", short = "x")]
    hash: Option<Hash>,

    #[options(help = "trusted header height", short = "h")]
    height: Option<Height>,
}

#[derive(Clone, Debug)]
struct InitOptions {
    /// identifier of the chain
    chain_id: ChainId,

    /// trusted header hash
    trusted_hash: Hash,

    /// trusted header height
    trusted_height: Height,
}

impl InitOptions {
    fn from_init_cmd(cmd: &InitCmd) -> Result<InitOptions, &'static str> {
        match (cmd.chain_id, cmd.hash, cmd.height) {
            (Some(chain_id), Some(hash), Some(height)) => Ok(Self {
                chain_id,
                trusted_hash: hash,
                trusted_height: height,
            }),
            (None, _, _) => Err("missing chain identifier"),
            (_, None, _) => Err("missing trusted hash"),
            (_, _, None) => Err("missing trusted height"),
        }
    }
}

impl Runnable for InitCmd {
    /// Initialize the light client for the given chain
    fn run(&self) {
        let config = app_config();

        let options = match InitOptions::from_init_cmd(self) {
            Ok(opts) => opts,
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
        };

        let chain_config = match config.chains.iter().find(|c| c.id == options.chain_id) {
            Some(config) => config,
            None => {
                status_err!("could not find config for chain: {}", options.chain_id);
                return;
            }
        };

        let trust_options = TrustOptions::new(
            options.trusted_hash,
            options.trusted_height,
            chain_config.trusting_period,
            TrustThreshold::default(),
        )
        .unwrap(); // FIXME(unwrap)

        let mut config = LightConfig::load_from_disk(LIGHT_CONFIG_PATH).unwrap(); // FIXME(unwrap)
        config.chains.insert(chain_config.id, trust_options);
        config.save_to_disk(LIGHT_CONFIG_PATH).unwrap(); // FIXME(unwrap)

        status_ok!(
            chain_config.id,
            "Set trusted options: hash={} height={}",
            options.trusted_hash,
            options.trusted_height
        );
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
