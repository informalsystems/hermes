use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{KeyRing, Store},
};

use crate::application::app_config;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Parser)]
pub struct KeysDeleteCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(long = "key-name", value_name = "KEY_NAME", help = "Name of the key")]
    key_name: Option<String>,

    #[clap(long = "all", help = "Delete all keys")]
    all: bool,
}

impl KeysDeleteCmd {
    fn options(
        &self,
        config: &Config,
    ) -> Result<KeysDeleteOptions<'_>, Box<dyn std::error::Error>> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))?;

        let id = match (self.all, &self.key_name) {
            (true, Some(_)) => {
                return Err("cannot set both --key-name and --all".to_owned().into());
            }
            (false, None) => {
                return Err("must provide either --key-name or --all".to_owned().into());
            }
            (true, None) => KeysDeleteId::All,
            (false, Some(ref key_name)) => KeysDeleteId::Named(key_name),
        };

        Ok(KeysDeleteOptions {
            config: chain_config.clone(),
            id,
        })
    }
}

#[derive(Clone, Debug)]
struct KeysDeleteOptions<'a> {
    id: KeysDeleteId<'a>,
    config: ChainConfig,
}

#[derive(Clone, Debug)]
enum KeysDeleteId<'a> {
    All,
    Named(&'a str),
}

impl Runnable for KeysDeleteCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.options(&config) {
            Err(err) => Output::error(err).exit(),
            Ok(result) => result,
        };

        match opts.id {
            KeysDeleteId::All => match delete_all_keys(&opts.config) {
                Ok(_) => {
                    Output::success_msg(format!("Removed all keys on chain {}", opts.config.id))
                        .exit()
                }
                Err(e) => Output::error(format!("{}", e)).exit(),
            },
            KeysDeleteId::Named(key_name) => match delete_key(&opts.config, key_name) {
                Ok(_) => Output::success_msg(format!(
                    "Removed key ({}) on chain {}",
                    key_name, opts.config.id
                ))
                .exit(),
                Err(e) => Output::error(format!("{}", e)).exit(),
            },
        };
    }
}

pub fn delete_key(config: &ChainConfig, key_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    keyring.remove_key(key_name)?;
    Ok(())
}

pub fn delete_all_keys(config: &ChainConfig) -> Result<(), Box<dyn std::error::Error>> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    let keys = keyring.keys()?;
    for key in keys {
        keyring.remove_key(&key.0)?;
    }
    Ok(())
}
