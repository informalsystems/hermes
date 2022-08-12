use abscissa_core::{
    clap::Parser,
    {Command, Runnable},
};
use chain_registry::relayer_config::get_configs;

use crate::conclude::Output;

use ibc_relayer::{
    config::{store, ChainConfig, Config},
    keyring::{KeyRing, Store::Test},
};

use std::path::PathBuf;
use tokio::runtime::Builder;
use tracing::{info, warn};

fn find_key(chainconfig: &ChainConfig) -> Option<String> {
    if let Ok(keyring) = KeyRing::new(Test, &chainconfig.account_prefix, &chainconfig.id) {
        if let Ok(keys) = keyring.keys() {
            if let Some((name, _)) = keys.first() {
                Some(name.to_string())
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The data structure that represents the arguments when invoking the `config auto` CLI command.
///
/// The command has two required arguments and an optional one which is used to manually specify the keys to use in the config file:
///
/// `config auto [OPTIONS] --path <PATH> --chain <CHAIN_NAME_1 CHAIN_NAME_2...>`
///
/// OR
///
/// `config auto [OPTIONS] --path <PATH> --chain <CHAIN_NAME_1 CHAIN_NAME_2...> --keys <KEY_NAME_1 KEY_NAME_2...>`
///
/// If no keys are specified, the first key stored in the KEYSTORE_DEFAULT_FOLDER will be used.
/// If keys are specified then there must be a key for every chain and the command will not verify that those keys exist.
#[derive(Clone, Command, Debug, Parser, PartialEq)]
#[clap(
    override_usage = "hermes config auto [OPTIONS] --chains <CHAIN_NAME_1 CHAIN_NAME_2> [--keys <CHAIN_NAME_1 CHAIN_NAME_2...>]"
)]
pub struct AutoCmd {
    #[clap(
        long = "path",
        required = true,
        value_name = "PATH",
        help_heading = "REQUIRED",
        help = "Path to the configuration file"
    )]
    path: PathBuf,

    #[clap(
        long = "chains",
        required = true,
        multiple = true,
        value_name = "CHAIN_NAME_1 CHAIN_NAME_2...",
        help_heading = "REQUIRED",
        help = "Names of the chains to include in the config. Every chain must be in the chain registry."
    )]
    chain_names: Vec<String>,

    #[clap(
        long = "keys",
        multiple = true,
        value_name = "KEY_CHAIN_1 KEY_CHAIN_2...",
        help = "Key names to include in the config. A key must be provided from every chain."
    )]
    keys: Option<Vec<String>>,
}

impl Runnable for AutoCmd {
    fn run(&self) {
        // Assert that for every chain, a key name is provided
        let runtime = Builder::new_current_thread().enable_all().build().unwrap();

        let (sorted_chains, sorted_keys): (Vec<String>, Option<Vec<String>>) = match &self.keys {
            Some(keys) => {
                // Sort chains and keys together
                let mut chain_key_tuples: Vec<(String, String)> = self
                    .chain_names
                    .iter()
                    .cloned()
                    .zip(keys.iter().cloned())
                    .collect();

                chain_key_tuples.sort_by(|a, b| (a.0.cmp(&b.0)));
                let (sorted_chains, sorted_keys): (Vec<String>, Vec<String>) =
                    chain_key_tuples.into_iter().unzip();

                (sorted_chains, Some(sorted_keys))
            }
            None => {
                let mut sorted_chains: Vec<String> = self.chain_names.to_vec();
                sorted_chains.sort();
                (sorted_chains, None)
            }
        };

        // Fetch chain configs
        match runtime.block_on(get_configs(&sorted_chains)) {
            Ok(mut chain_configs) => {
                if let Some(keys) = sorted_keys {
                    for (mut chain_config, key_name) in
                        chain_configs.iter_mut().zip(keys.into_iter())
                    {
                        info!("{}: uses key \"{}\"", &chain_config.id, &key_name);
                        chain_config.key_name = key_name;
                    }
                } else {
                    for mut chain_config in chain_configs.iter_mut() {
                        let chain_id = &chain_config.id;
                        let key = find_key(chain_config);
                        if let Some(key) = key {
                            info!("{}: uses key \"{}\"", &chain_id, &key);
                            chain_config.key_name = key;
                        } else {
                            warn!("No key found for chain: {}", chain_id);
                        }
                    }
                }

                let config = Config {
                    chains: chain_configs,
                    ..Config::default()
                };

                match store(&config, &self.path) {
                    Ok(_) => {
                        warn!("Gas parameters are set to default values.");
                        Output::success(format!(
                            "Config file written successfully : {}.",
                            self.path.to_str().unwrap()
                        ))
                        .exit()
                    }
                    Err(e) => Output::error(e.to_string()).exit(),
                }
            }
            Err(e) => {
                Output::error(e.to_string()).exit();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::AutoCmd;
    use abscissa_core::clap::Parser;
    use std::path::PathBuf;

    #[test]
    fn test_auto_config_with_keys() {
        assert_eq!(
            AutoCmd {
                path: PathBuf::from("./example.toml"),
                chain_names: vec!["chain1".to_string(), "chain2".to_string()],
                keys: Some(vec!["key1".to_string(), "key2".to_string()]),
            },
            AutoCmd::parse_from(&[
                "test",
                "--path",
                "./example.toml",
                "--chains",
                "chain1",
                "chain2",
                "--keys",
                "key1",
                "key2"
            ])
        )
    }

    #[test]
    fn test_auto_config_without_keys() {
        assert_eq!(
            AutoCmd {
                path: PathBuf::from("./example.toml"),
                chain_names: vec!["chain1".to_string(), "chain2".to_string()],
                keys: None,
            },
            AutoCmd::parse_from(&[
                "test",
                "--path",
                "./example.toml",
                "--chains",
                "chain1",
                "chain2"
            ])
        )
    }
}
