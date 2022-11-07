use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use eyre::eyre;
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{KeyRing, Store},
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::application::app_config;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
#[clap(
    override_usage = "hermes keys delete --chain <CHAIN_ID> --key-name <KEY_NAME>

    hermes keys delete --chain <CHAIN_ID> --all"
)]
pub struct KeysDeleteCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "FLAGS",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "key-name",
        required = true,
        value_name = "KEY_NAME",
        group = "delete_mode",
        help_heading = "FLAGS",
        help = "Name of the key"
    )]
    key_name: Option<String>,

    #[clap(
        long = "all",
        required = true,
        group = "delete_mode",
        help_heading = "FLAGS",
        help = "Delete all keys"
    )]
    all: bool,
}

impl KeysDeleteCmd {
    fn options(&self, config: &Config) -> eyre::Result<KeysDeleteOptions<'_>> {
        let chain_config = config
            .find_chain(&self.chain_id)
            .ok_or_else(|| eyre!("chain '{}' not found in configuration file", self.chain_id))?;

        let id = match (self.all, &self.key_name) {
            (true, None) => KeysDeleteId::All,
            (false, Some(ref key_name)) => KeysDeleteId::Named(key_name),
            // This case should never trigger.
            // The 'required' parameter for the flags will trigger an error if both flags have not been given.
            // And the 'group' parameter for the flags will trigger an error if both flags are given.
            _ => Output::error("--key-name and --all can't both be set or both None".to_string())
                .exit(),
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

pub fn delete_key(config: &ChainConfig, key_name: &str) -> eyre::Result<()> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    keyring.remove_key(key_name)?;
    Ok(())
}

pub fn delete_all_keys(config: &ChainConfig) -> eyre::Result<()> {
    let mut keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    let keys = keyring.keys()?;
    for key in keys {
        keyring.remove_key(&key.0)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::KeysDeleteCmd;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_keys_delete_key_name() {
        assert_eq!(
            KeysDeleteCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: Some("to_delete".to_owned()),
                all: false
            },
            KeysDeleteCmd::parse_from(["test", "--chain", "chain_id", "--key-name", "to_delete"])
        )
    }

    #[test]
    fn test_keys_delete_all() {
        assert_eq!(
            KeysDeleteCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: None,
                all: true
            },
            KeysDeleteCmd::parse_from(["test", "--chain", "chain_id", "--all"])
        )
    }

    #[test]
    fn test_keys_delete_only_chain() {
        assert!(KeysDeleteCmd::try_parse_from(["test", "--chain", "chain_id"]).is_err())
    }

    #[test]
    fn test_keys_delete_key_name_or_all() {
        assert!(KeysDeleteCmd::try_parse_from([
            "test",
            "--chain",
            "chain_id",
            "--key-name",
            "to_delete",
            "--all"
        ])
        .is_err())
    }

    #[test]
    fn test_keys_delete_no_chain() {
        assert!(KeysDeleteCmd::try_parse_from(["test", "--all"]).is_err())
    }
}
