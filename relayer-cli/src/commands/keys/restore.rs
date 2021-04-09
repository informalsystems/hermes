use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::Config;
use ibc_relayer::keys::restore::{restore_key, KeysRestoreOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::Kind;

#[derive(Clone, Command, Debug, Options)]
pub struct KeyRestoreCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(short = "n", required, help = "key name")]
    name: String,

    #[options(short = "m", required, help = "mnemonic to restore the key from")]
    mnemonic: String,
}

impl KeyRestoreCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysRestoreOptions, String> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let name = self.name.clone();
        // .ok_or_else(|| "missing key name".to_string())?;

        let mnemonic = self.mnemonic.clone();
        // .ok_or_else(|| "missing mnemonic".to_string())?;

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

        let res = restore_key(opts).map_err(|e| Kind::Keys.context(e));

        match res {
            Ok(msg) => Output::success_msg(msg).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
