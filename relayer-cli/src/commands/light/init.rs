use std::{future::Future, ops::Deref};

use crate::light::config::{LightConfig, LIGHT_CONFIG_PATH};
use crate::prelude::*;

use abscissa_core::{application::fatal_error, error::BoxError, Command, Options, Runnable};

use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint_light_client::types::TrustThreshold;

use relayer::client::trust_options::TrustOptions;

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

impl InitCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config();

        let options =
            InitOptions::from_init_cmd(self).map_err(|e| format!("invalid options: {}", e))?;

        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == options.chain_id)
            .ok_or_else(|| format!("could not find config for chain: {}", options.chain_id))?;

        let trust_options = TrustOptions::new(
            options.trusted_hash,
            options.trusted_height,
            chain_config.trusting_period,
            TrustThreshold::default(),
        )?;

        let mut config = LightConfig::load(LIGHT_CONFIG_PATH)?;
        config.chains.insert(chain_config.id, trust_options);
        config.save(LIGHT_CONFIG_PATH)?;

        status_ok!(
            chain_config.id,
            "Set trusted options: hash={} height={}",
            options.trusted_hash,
            options.trusted_height
        );

        Ok(())
    }
}

impl Runnable for InitCmd {
    /// Initialize the light client for the given chain
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
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
