use std::path::PathBuf;

use abscissa_core::{Command, Options, Runnable};

use anomaly::BoxError;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::config::Config;
use ibc_relayer::keys::add::{add_key, KeySource, KeysAddOptions};

use crate::application::app_config;
use crate::conclude::Output;
use crate::error::Kind;

#[derive(Clone, Command, Debug, Options)]
pub struct KeysAddCmd {
    #[options(free, help = "identifier of the chain")]
    chain_id: Option<ChainId>,

    #[options(
        short = "f",
        help = "the path to the key file (conflicts with --mnemonic)"
    )]
    file: Option<PathBuf>,

    #[options(short = "m", help = "the BIP-49 mnemonic (conflicts with --file)")]
    mnemonic: Option<String>,
}

impl KeysAddCmd {
    fn validate_options(&self, config: &Config) -> Result<KeysAddOptions, BoxError> {
        let chain_id = self
            .chain_id
            .as_ref()
            .ok_or("missing required chain identifier option")?;

        let chain_config = config
            .find_chain(chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", chain_id))?;

        if self.file.is_some() && self.mnemonic.is_some() {
            return Err("the --file and --mnemonic options are mutually exclusive".into());
        }

        if let Some(ref file) = self.file {
            Ok(KeysAddOptions {
                name: chain_config.key_name.clone(),
                config: chain_config.clone(),
                source: KeySource::File(file.clone()),
            })
        } else if let Some(ref mnemonic) = self.mnemonic {
            Ok(KeysAddOptions {
                name: chain_config.key_name.clone(),
                config: chain_config.clone(),
                source: KeySource::Mnemonic(mnemonic.clone()),
            })
        } else {
            Err("either the --file or --mnemonic option is required".into())
        }
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
