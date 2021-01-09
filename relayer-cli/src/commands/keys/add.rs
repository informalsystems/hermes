use crate::application::app_config;
use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;

use crate::error::{Error, Kind};
use crate::prelude::*;
use relayer::keys::add::{add_key, KeysAddOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct KeysAddCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,

    #[options(free, help = "the key path and filename")]
    file: Option<String>,
}

impl KeysAddCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysAddOptions, String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "missing chain identifier".to_string())?;

        let chain_config = config
            .find_chain(&chain_id.parse().unwrap())
            .ok_or_else(|| {
                "Invalid chain identifier. Cannot retrieve the chain configuration".to_string()
            })?;

        let key_filename = self
            .file
            .clone()
            .ok_or_else(|| "missing signer key file".to_string())?;

        Ok(KeysAddOptions {
            name: chain_config.key_name.clone(),
            file: key_filename,
            chain_config: chain_config.clone(),
        })
    }
}

impl Runnable for KeysAddCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };

        let res: Result<String, Error> = add_key(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => status_info!("key add result: ", "{:?}", r),
            Err(e) => status_info!("key add failed: ", "{}", e),
        }
    }
}
