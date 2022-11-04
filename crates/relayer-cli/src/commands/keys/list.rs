use alloc::collections::btree_map::BTreeMap as HashMap;
use core::fmt::Write;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::conclude::Output;
use crate::{application::app_config, conclude::json};
use ibc_relayer::{
    config::{ChainConfig, Config},
    keyring::{KeyEntry, KeyRing, Store},
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct KeysListCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain"
    )]
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
            Err(err) => Output::error(err).exit(),
            Ok(result) => result,
        };

        match list_keys(opts.chain_config) {
            Ok(keys) if json() => {
                let keys = keys.into_iter().collect::<HashMap<_, _>>();
                Output::success(keys).exit()
            }
            Ok(keys) => {
                let mut msg = String::new();
                for (name, key) in keys {
                    let _ = write!(msg, "\n- {} ({})", name, key.account);
                }
                Output::success_msg(msg).exit()
            }
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct KeysListOptions {
    pub chain_config: ChainConfig,
}

pub fn list_keys(config: ChainConfig) -> eyre::Result<Vec<(String, KeyEntry)>> {
    let keyring = KeyRing::new(Store::Test, &config.account_prefix, &config.id)?;
    let keys = keyring.keys()?;
    Ok(keys)
}

#[cfg(test)]
mod tests {
    use super::KeysListCmd;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_keys_list() {
        assert_eq!(
            KeysListCmd {
                chain_id: ChainId::from_string("chain_id")
            },
            KeysListCmd::parse_from(["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_keys_list_no_chain() {
        assert!(KeysListCmd::try_parse_from(["test"]).is_err())
    }
}
