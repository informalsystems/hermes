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
pub struct KeyRestoreCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(short = "m", required, help = "mnemonic to restore the key from")]
    mnemonic: String,
}

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub mnemonic: String,
    pub config: ChainConfig,
}

impl KeyRestoreCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysRestoreOptions, String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        Ok(KeysRestoreOptions {
            mnemonic: self.mnemonic.clone(),
            config: chain_config.clone(),
        })
    }
}

impl Runnable for KeyRestoreCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let key_name = opts.config.key_name.clone();
        let chain_id = opts.config.id.clone();
        let key = restore_key(&opts.mnemonic, opts.config);

        match key {
            Ok(key) => Output::success_msg(format!(
                "Restored key '{}' ({}) on chain {}",
                key_name, key.account, chain_id
            ))
            .exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn restore_key(mnemonic: &str, config: ChainConfig) -> Result<KeyEntry, BoxError> {
    let mut keyring = KeyRing::new(Store::Disk, config)?;
    let key_entry = keyring.key_from_mnemonic(mnemonic)?;
    keyring.add_key(key_entry.clone())?;

    Ok(key_entry)
}
