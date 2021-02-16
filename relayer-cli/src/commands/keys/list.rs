use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::Config;
use ibc_relayer::keys::list::{list_keys, KeysListOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct KeysListCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: ChainId,
}

impl KeysListCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysListOptions, String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        Ok(KeysListOptions {
            chain_config: chain_config.clone(),
        })
    }
}

impl Runnable for KeysListCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let res: Result<String, Error> = list_keys(opts).map_err(|e| Kind::Keys.context(e).into());

        match res {
            Ok(r) => Output::success(r).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
