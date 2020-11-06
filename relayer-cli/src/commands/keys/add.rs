use crate::application::app_config;
use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;

use crate::error::{Error, Kind};
use crate::prelude::*;
use relayer::keys::add::{add_key, KeysAddOptions};
use std::fs;
use std::path::Path;

#[derive(Clone, Command, Debug, Options)]
pub struct KeyAddCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,

    #[options(free, help = "the key name")]
    name: Option<String>,

    #[options(free, help = "the key path and filename")]
    file: Option<String>,
}

impl KeyAddCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysAddOptions, String> {
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

        let key_name = self
            .name
            .clone()
            .ok_or_else(|| "missing key name".to_string())?;

        // Get content of key seed file
        let key_filename = self
            .file
            .clone()
            .ok_or_else(|| "missing signer key file".to_string())?;

        let key_file = Path::new(&key_filename).exists();
        if !key_file {
            return Err("cannot find key file specified".to_string());
        }

        let key_file_contents = fs::read_to_string(key_filename)
            .expect("Something went wrong reading the key seed file");

        Ok(KeysAddOptions {
            name: key_name,
            file: key_file_contents,
            chain_config: chain_config.clone(),
        })
    }
}

impl Runnable for KeyAddCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };

        let res: Result<Vec<u8>, Error> = add_key(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => status_info!("key add result: ", "{:?}", r),
            Err(e) => status_info!("key add failed: ", "{}", e),
        }
    }
}
