use abscissa_core::{Command, Options, Runnable};
use anomaly::BoxError;

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{KeyEntry, KeyRing, Store},
};

use crate::application::app_config;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysListCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,
}

impl KeysListCmd {
    fn options(&self, config: &Config) -> Result<KeysListOptions, String> {
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

        let opts = match self.options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let chain_config = opts.chain_config.clone();
        let key = list_keys(opts.chain_config);

        match key {
            Ok(key) => Output::success_msg(format!(
                "chain: {} -> {} ({})",
                chain_config.id, chain_config.key_name, key.account,
            ))
            .exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct KeysListOptions {
    pub chain_config: ChainConfig,
}

pub fn list_keys(config: ChainConfig) -> Result<KeyEntry, BoxError> {
    let keyring = KeyRing::new(Store::Test, config)?;
    let key_entry = keyring.get_key()?;
    Ok(key_entry)
}
