use abscissa_core::{Command, Options, Runnable};
use eyre::{eyre, WrapErr};

use relayer::config::Config;
use relayer::keys::restore::{restore_key, KeysRestoreOptions};

use crate::application::app_config;
use crate::error::ErrorMsg;
use crate::prelude::*;

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
    fn validate_options(&self, config: &Config) -> eyre::Result<KeysRestoreOptions> {
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

        let key_name = self.name.clone().ok_or_else(|| eyre!("missing key name"))?;

        let mnemonic_words = self
            .mnemonic
            .clone()
            .ok_or_else(|| eyre!("missing mnemonic"))?;

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
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };

        let res = restore_key(opts).wrap_err(ErrorMsg::Keys); // todo: maybe unnecessary error chaining? remove.

        match res {
            Ok(r) => status_info!("key restore result: ", "{:?}", hex::encode(r)),
            Err(e) => status_info!("key restore failed: ", "{}", e),
        }
    }
}
