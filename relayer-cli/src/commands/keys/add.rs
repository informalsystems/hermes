use std::{
    fs,
    path::{Path, PathBuf},
};

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
pub struct KeysAddCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(short = "f", required, help = "path to the key file")]
    file: PathBuf,
}

impl KeysAddCmd {
    fn options(&self, config: &Config) -> Result<KeysAddOptions, BoxError> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        Ok(KeysAddOptions {
            name: chain_config.key_name.clone(),
            config: chain_config.clone(),
            file: self.file.clone(),
        })
    }
}

#[derive(Clone, Debug)]
pub struct KeysAddOptions {
    pub name: String,
    pub config: ChainConfig,
    pub file: PathBuf,
}

impl Runnable for KeysAddCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let chain_id = opts.config.id.clone();
        let key = add_key(opts.config, &opts.file);

        match key {
            Ok(key) => Output::success_msg(format!(
                "Added key '{}' ({}) on chain {}",
                opts.name, key.account, chain_id
            ))
            .exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn add_key(config: ChainConfig, file: &Path) -> Result<KeyEntry, BoxError> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;

    let key_contents = fs::read_to_string(file).map_err(|_| "error reading the key file")?;
    let key = keyring.key_from_seed_file(&key_contents)?;

    keyring.add_key(&config.key_name, key.clone())?;

    Ok(key)
}
