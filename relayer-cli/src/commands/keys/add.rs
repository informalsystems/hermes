use std::path::PathBuf;

use abscissa_core::{Command, Options, Runnable};

use anomaly::BoxError;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::Config;
use ibc_relayer::keys::add::{add_key, KeysAddOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::Kind;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysAddCmd {
    #[options(free, required, help = "identifier of the chain")]
    chain_id: ChainId,

    #[options(short = "f", required, help = "path to the key file")]
    file: PathBuf,
}

impl KeysAddCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysAddOptions, BoxError> {
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

impl Runnable for KeysAddCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let res = add_key(opts).map_err(|e| Kind::Keys.context(e));

        match res {
            Ok(r) => Output::success_msg(r).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
