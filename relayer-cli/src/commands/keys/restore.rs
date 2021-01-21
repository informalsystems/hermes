use abscissa_core::{Command, Options, Runnable};

use relayer::config::Config;
use relayer::keys::restore::{restore_key, KeysRestoreOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct KeyRestoreCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<String>,

    #[options(free, help = "the key name")]
    name: Option<String>,

    #[options(free, help = "mnemonic to add key")]
    mnemonic: Option<String>,
}

impl KeyRestoreCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysRestoreOptions, String> {
        let chain_id = self
            .chain_id
            .clone()
            .ok_or_else(|| "missing chain identifier".to_string())?;

        let chain_config = config
            .find_chain(&chain_id.parse().unwrap())
            .ok_or_else(|| {
                "Invalid chain identifier. Cannot retrieve the chain configuration".to_string()
            })?;

        let key_name = self
            .name
            .clone()
            .ok_or_else(|| "missing key name".to_string())?;

        let mnemonic_words = self
            .mnemonic
            .clone()
            .ok_or_else(|| "missing mnemonic".to_string())?;

        Ok(KeysRestoreOptions {
            name: key_name,
            mnemonic: mnemonic_words,
            chain_config: chain_config.clone(),
        })
    }
}

impl Runnable for KeyRestoreCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };

        let res: Result<Vec<u8>, Error> =
            restore_key(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => Output::success(r).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
