use crate::application::app_config;
use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;

use crate::error::{Error, Kind};
use crate::prelude::*;
use relayer::keys::list::{list_keys, KeysListOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct KeysListCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,
}

impl KeysListCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysListOptions, String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "missing chain identifier".to_string())?;

        let chain_config = config
            .chains
            .iter()
            .find(|c| c.id == chain_id.parse().unwrap())
            .ok_or_else(|| {
                "Invalid chain identifier. Cannot retrieve the chain configuration".to_string()
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

        let res: Result<String, Error> = list_keys(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => status_info!("keys list result: ", "{:?}", r),
            Err(e) => status_info!("keys list failed: ", "{}", e),
        }
    }
}
