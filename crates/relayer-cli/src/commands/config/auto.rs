use crate::chain_registry::get_configs;
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use itertools::Itertools;

use crate::conclude::Output;

use ibc_relayer::config::{store, ChainConfig, Config};

use std::collections::HashSet;
use std::path::PathBuf;
use tracing::{info, warn};

fn find_key(chain_config: &ChainConfig) -> Option<String> {
    let keys = chain_config.list_keys().ok()?;
    keys.into_iter().next().map(|(name, _)| name)
}

/// The data structure that represents the arguments when invoking the `config auto` CLI command.
///
/// The command has two required arguments and an optional one which is used to manually specify commit hash of the chain-registry from which the chain configs will be generated:
///
/// `config auto [OPTIONS] --output <PATH> --chains <CHAIN_NAME_1[:<KEY_1>] CHAIN_NAME_2[:<KEY_2>]...> [--commit <COMMIT_HASH>]`
///
/// If no key is specified, the first key stored in the KEYSTORE_DEFAULT_FOLDER, if it exists, will be used otherwise the field `key_name` will be left empty.
/// If a is specified then it will be used without verifying that it exists.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
#[clap(
    override_usage = "hermes config auto [OPTIONS] --output <PATH> --chain <CHAIN1_NAME:OPTIONAL_KEY_NAME> --chain <CHAIN2_NAME:OPTIONAL_KEY_NAME>"
)]
pub struct AutoCmd {
    #[clap(
        long = "output",
        required = true,
        value_name = "PATH",
        help_heading = "REQUIRED",
        help = "Path to the configuration file"
    )]
    path: PathBuf,

    #[clap(
        long = "chains",
        alias = "chain",
        required = true,
        multiple = true,
        value_name = "CHAIN_NAME:OPTIONAL_KEY_NAME",
        help_heading = "REQUIRED",
        help = "Names of the chains to include in the configuration, together with an optional key name. \
                Either repeat this argument for every chain or pass a space-separated list of chains. \
                Every chain must be found in the chain registry."
    )]
    chain_names: Vec<String>,

    #[clap(
        long = "commit",
        value_name = "COMMIT_HASH",
        help = "Commit hash from which the chain configs will be generated. If it's not set, the latest commit will be used."
    )]
    commit: Option<String>,
}

fn extract_chains_and_keys(chain_names: &[String]) -> Vec<(String, Option<String>)> {
    let mut captured_names = chain_names
        .iter()
        .map(|chain_key| {
            chain_key
                .split_once(':')
                .map(|(name, key)| (name.to_string(), Some(key.to_string())))
                .unwrap_or_else(|| (chain_key.to_string(), None))
        })
        .collect::<Vec<_>>();

    captured_names.sort_by(|a, b| a.0.cmp(&b.0));
    captured_names
}

impl Runnable for AutoCmd {
    fn run(&self) {
        // Assert that for every chain, a key name is provided
        let runtime = tokio::runtime::Runtime::new().unwrap();

        // Extract keys and sort chains by name
        let names_and_keys = extract_chains_and_keys(&self.chain_names);

        let chain_names = names_and_keys
            .iter()
            .map(|(n, _)| n)
            .cloned()
            .collect::<Vec<_>>();

        let commit = self.commit.clone();

        // Fetch chain configs from the chain registry
        let config_results = runtime.block_on(get_configs(&chain_names, commit));

        if let Err(e) = config_results {
            let config = Config::default();

            match store(&config, &self.path) {
                Ok(_) => Output::error(format!(
                    "An error occurred while generating the chain config file: {}
                    A default config file has been written at '{}'",
                    e,
                    self.path.display(),
                ))
                .exit(),
                Err(e) => Output::error(format!(
                    "An error occurred while attempting to write the config file: {}",
                    e
                ))
                .exit(),
            }
        };

        let mut chain_configs: Vec<(String, ChainConfig)> = config_results
            .unwrap()
            .into_iter()
            .filter_map(|(name, config)| config.ok().map(|c| (name, c)))
            .collect();

        // Determine which chains were not fetched
        let fetched_chains_set: HashSet<_> =
            HashSet::from_iter(chain_configs.iter().map(|(name, _)| name).cloned());
        let expected_chains_set: HashSet<_> = HashSet::from_iter(chain_names.iter().cloned());

        let missing_chains_set: HashSet<_> = expected_chains_set
            .difference(&fetched_chains_set)
            .collect();

        let configs_and_keys = chain_configs
            .iter_mut()
            .zip(names_and_keys.iter().map(|(_, keys)| keys).cloned());

        for ((_name, chain_config), key_option) in configs_and_keys {
            // If a key is provided, use it
            if let Some(key_name) = key_option {
                info!("{}: uses key \"{}\"", &chain_config.id(), &key_name);
                chain_config.set_key_name(key_name);
            } else {
                // Otherwise, find the key in the keystore
                let chain_id = &chain_config.id();
                let key = find_key(chain_config);
                if let Some(key_name) = key {
                    info!("{}: uses key '{}'", &chain_id, &key_name);
                    chain_config.set_key_name(key_name);
                } else {
                    // If no key is found, warn the user and continue
                    warn!("No key found for chain: {}", chain_id);
                }
            }
        }

        let config = Config {
            chains: chain_configs.into_iter().map(|(_, c)| c).collect(),
            ..Config::default()
        };

        match store(&config, &self.path) {
            Ok(_) if missing_chains_set.is_empty() => {
                Output::success_msg(format!(
                    "Config file written successfully at '{}'",
                    self.path.display()
                ))
                .exit()
            },
            Ok(_) => {
                Output::success_msg(format!(
                    "Config file written successfully at '{}'. \
                    However, configurations for the following chains were not able to be generated: {}",
                    self.path.display(),
                    missing_chains_set.iter().join(", "),
                ))
                .exit()
            },
            Err(e) => Output::error(format!(
                "An error occurred while attempting to write the config file: {}",
                e
            ))
            .exit(),
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
            AutoCmd::parse_from([
                "test",
                "--output",
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
            AutoCmd::parse_from([
                "test",
                "--output",
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
