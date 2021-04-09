use abscissa_core::{Command, Options, Runnable};

use anomaly::BoxError;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::store::{KeyEntry, KeyRing, Store},
};

use crate::application::app_config;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Options)]
pub struct KeyRestoreCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(short = "n", required, help = "key name")]
    name: String,

    #[options(short = "m", required, help = "mnemonic to restore the key from")]
    mnemonic: String,
}

#[derive(Clone, Debug)]
pub struct KeysRestoreOptions {
    pub name: String,
    pub mnemonic: String,
    pub config: ChainConfig,
}

impl KeyRestoreCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysRestoreOptions, String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let name = self.name.clone();
        let mnemonic = self.mnemonic.clone();

        Ok(KeysRestoreOptions {
            name,
            mnemonic,
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

        let chain_id = opts.config.id.clone();
        let key = restore_key(&opts.name, &opts.mnemonic, opts.config);

        match key {
            Ok(key) => Output::success_msg(format!(
                "Restored key '{}' ({}) on chain {}",
                opts.name, key.account, chain_id
            ))
            .exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn restore_key(name: &str, mnemonic: &str, config: ChainConfig) -> Result<KeyEntry, BoxError> {
    let mut keyring = KeyRing::new(Store::Disk, config)?;
    let key_entry = keyring.key_from_mnemonic(mnemonic)?;
    keyring.add_key(key_entry.clone())?;

    Ok(key_entry)
}
