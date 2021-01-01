use abscissa_core::{Command, Options, Runnable};
use eyre::{eyre, WrapErr};

use relayer::config::Config;
use relayer::keys::add::{add_key, KeysAddOptions};

use crate::application::app_config;
use crate::error::ErrorMsg;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysAddCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,

    #[options(free, help = "the key path and filename")]
    file: Option<String>,
}

impl KeysAddCmd {
    fn validate_options(&self, config: &Config) -> eyre::Result<KeysAddOptions> {
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

        let key_filename = self
            .file
            .clone()
            .ok_or_else(|| eyre!("missing signer key file"))?;

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

        let res = add_key(opts).wrap_err(ErrorMsg::Keys); // todo: maybe unnecessary error chaining, remove it.

        match res {
            Ok(r) => status_info!("key add result: ", "{:?}", r),
            Err(e) => status_info!("key add failed: ", "{}", e),
        }
    }
}
