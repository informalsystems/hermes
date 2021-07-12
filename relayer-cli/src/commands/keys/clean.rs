use abscissa_core::{Command, Options, Runnable};
use anomaly::BoxError;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{KeyRing, Store},
};

use crate::application::app_config;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysCleanCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(
        short = "n",
        help = "name of the key (defaults to the `key_name` defined in the config)"
    )]
    name: Option<String>,
}

impl KeysCleanCmd {
    fn options(&self, config: &Config) -> Result<KeysCleanOptions, BoxError> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let name = self
            .name
            .clone()
            .unwrap_or_else(|| chain_config.key_name.clone());

        Ok(KeysCleanOptions {
            config: chain_config.clone(),
            name,
        })
    }
}

#[derive(Clone, Debug)]
pub struct KeysCleanOptions {
    pub name: String,
    pub config: ChainConfig,
}

impl Runnable for KeysCleanCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        match clean_key(&opts.config, &opts.name) {
            Ok(_) => Output::success_msg(format!(
                "Removed key '{}' on chain {}",
                opts.name, opts.config.id
            ))
            .exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn clean_key(config: &ChainConfig, key_name: &str) -> Result<(), BoxError> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    keyring.remove_key(key_name)?;
    Ok(())
}
