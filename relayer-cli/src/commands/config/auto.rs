use crate::chain_registry::get_configs;
use abscissa_core::{
    clap::Parser,
    {Command, Runnable},
};

use crate::conclude::Output;

use ibc_relayer::{
    config::{store, ChainConfig, Config},
    keyring::{KeyRing, Store::Test},
};

use regex::Regex;

use std::path::PathBuf;
use tokio::runtime::Builder;
use tracing::{info, warn};

fn find_key(chainconfig: &ChainConfig) -> Option<String> {
    if let Ok(keyring) = KeyRing::new(Test, &chainconfig.account_prefix, &chainconfig.id) {
        if let Ok(keys) = keyring.keys() {
            if let Some((name, _)) = keys.first() {
                return Some(name.to_string());
            }
        }
    }
    None
}

/// The data structure that represents the arguments when invoking the `config auto` CLI command.
///
/// The command has two required arguments and an optional one which is used to manually specify commit hash of the chain-registry from which the chain configs will be generated:
///
/// `config auto [OPTIONS] --path <PATH> --chains <CHAIN_NAME_1[:<KEY_1>] CHAIN_NAME_2[:<KEY_2>]...> [--commit <COMMIT_HASH>]`
///
/// If no key is specified, the first key stored in the KEYSTORE_DEFAULT_FOLDER, if it exists, will be used otherwise the field `key_name` will be left empty.
/// If a is specified then it will be used without verifying that it exists.
#[derive(Clone, Command, Debug, Parser, PartialEq)]
#[clap(
    override_usage = "hermes config auto [OPTIONS] --chains <CHAIN_NAME_1[:<KEY1>] CHAIN_NAME_2[:<KEY2>]> [--commit <COMMIT_HASH>]"
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
        long = "commit",
        value_name = "COMMIT_HASH",
        help = "Commit hash from which the chain configs will be generated. If it's not set, the latest commit will be used."
    )]
    commit: Option<String>,
}

impl Runnable for AutoCmd {
    fn run(&self) {
        // Assert that for every chain, a key name is provided
        let runtime = Builder::new_current_thread().enable_all().build().unwrap();

        // Extract keys and sort chains by name
        let re = Regex::new(r"^(?P<chain>\w+)(:?:(?P<key>\w+))?$").unwrap();
        let (sorted_chains, sorted_keys): (Vec<String>, Vec<Option<String>>) = {
            let mut captured_names: Vec<(String, Option<String>)> = self
                .chain_names
                .iter()
                .map(|chain_key| {
                    if let Some(captures) = &re.captures(chain_key) {
                        if let Some(name) = captures.name("chain") {
                            let name = name.as_str().to_string();
                            let key = captures.name("key").map(|key| key.as_str().to_string());
                            return (name, key);
                        }
                    }
                    Output::error(&format!(
                        "Invalid chain name: {}. Must be in the form of <chain_name>[:<key_name>]",
                        chain_key
                    ))
                    .exit();
                })
                .collect();
            captured_names.sort_by(|a, b| (a.0.cmp(&b.0)));
            captured_names.into_iter().unzip()
        };

        // Fetch chain configs from the chain registry
        let commit = self.commit.clone();
        match runtime.block_on(get_configs(&sorted_chains, commit)) {
            Ok(mut chain_configs) => {
                for (mut chain_config, key_option) in
                    chain_configs.iter_mut().zip(sorted_keys.into_iter())
                {
                    // If a key is provided, use it
                    if let Some(key_name) = key_option {
                        info!("{}: uses key \"{}\"", &chain_config.id, &key_name);
                        chain_config.key_name = key_name;
                    } else {
                        // Otherwise, find the key in the keystore
                        let chain_id = &chain_config.id;
                        let key = find_key(chain_config);
                        if let Some(key) = key {
                            info!("{}: uses key \"{}\"", &chain_id, &key);
                            chain_config.key_name = key;
                        } else {
                            // If no key is found, warn the user and continue
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
    fn auto_config_without_commit() {
        assert_eq!(
            AutoCmd {
                path: PathBuf::from("./example.toml"),
                chain_names: vec!["chain1:key1".to_string(), "chain2".to_string()],
                commit: None,
            },
            AutoCmd::parse_from(&[
                "test",
                "--path",
                "./example.toml",
                "--chains",
                "chain1:key1",
                "chain2",
            ])
        )
    }

    #[test]
    fn auto_config_with_commit() {
        assert_eq!(
            AutoCmd {
                path: PathBuf::from("./example.toml"),
                chain_names: vec!["chain1:key1".to_string(), "chain2".to_string()],
                commit: Some("test_commit".to_string()),
            },
            AutoCmd::parse_from(&[
                "test",
                "--path",
                "./example.toml",
                "--chains",
                "chain1:key1",
                "chain2",
                "--commit",
                "test_commit"
            ])
        )
    }
}
