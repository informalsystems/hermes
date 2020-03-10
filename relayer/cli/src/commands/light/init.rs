use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

use tendermint::chain::Id as ChainId;
use tendermint::hash::Hash;
use tendermint::lite::Height;

#[derive(Command, Debug, Options)]
pub struct InitCmd {
    #[options(free, help = "identifier of the chain to initialize light client for")]
    chain_id: Option<ChainId>,

    #[options(help = "trusted header hash", short = "x")]
    hash: Option<Hash>,

    #[options(help = "trusted header height", short = "h")]
    height: Option<Height>,
}

#[derive(Debug)]
struct InitOptions<'a> {
    /// identifier of chain to initialize light client for
    chain_id: &'a ChainId,

    /// trusted header hash
    trusted_hash: &'a Hash,

    /// trusted header height
    trusted_height: Height,
}

impl InitCmd {
    fn validate_options(&self) -> Result<InitOptions<'_>, &'static str> {
        match (&self.chain_id, &self.hash, self.height) {
            (Some(chain_id), Some(trusted_hash), Some(trusted_height)) => Ok(InitOptions {
                chain_id,
                trusted_hash,
                trusted_height,
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

        let opts = match self.validate_options() {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(opts) => opts,
        };

        status_info!("Config", "{:?}", *config);
        status_info!("Options", "{:?}", opts);
    }
}
