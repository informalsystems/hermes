use abscissa_core::{Command, Options, Runnable};

use relayer::config::Config;
use relayer::keys::add::{add_key, KeysAddOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::{Error, Kind};

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
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };

        let res: Result<String, Error> = add_key(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => Output::success(r).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
