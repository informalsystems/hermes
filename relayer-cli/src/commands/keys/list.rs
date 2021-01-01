use abscissa_core::{Command, Options, Runnable};
use eyre::{eyre, WrapErr};

use relayer::config::Config;
use relayer::keys::list::{list_keys, KeysListOptions};

use crate::application::app_config;
use crate::error::ErrorMsg;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysListCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,
}

impl KeysListCmd {
    fn validate_options(&self, config: &Config) -> eyre::Result<KeysListOptions> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| eyre!("missing chain identifier"))?;

        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == chain_id.parse().unwrap())
            .ok_or_else(|| {
                eyre!("Invalid chain identifier. Cannot retrieve the chain configuration")
            })?;

        Ok(KeysListOptions {
            chain_config: chain_config.clone(),
        })
    }
}

impl Runnable for KeysListCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };

        let res = list_keys(opts).wrap_err(ErrorMsg::Keys); // todo: maybe unnecessary error chaining, remove it.

        match res {
            Ok(r) => status_info!("keys list result: ", "{:?}", r),
            Err(e) => status_info!("keys list failed: ", "{}", e),
        }
    }
}
