use abscissa_core::{
    clap::Parser,
    {Command, Runnable},
};
use chain_registry::relayer_config::get_configs;

use crate::conclude::Output;

use ibc_relayer::{
    config::{store, Config},
    keyring::{KEYSTORE_DEFAULT_FOLDER, KEYSTORE_FILE_EXTENSION},
};

use std::{
    ffi::OsStr,
    fs::{self},
    path::PathBuf,
};
use tokio::runtime::Builder;
use tracing::warn;

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
fn find_key(chain_name: &str) -> Option<String> {
    println!("Finding key for chain {}", chain_name);
    let home_dir = match std::env::home_dir() {
        Some(home_dir) => home_dir.to_str().unwrap().to_string(),
        None => {
            Output::error("Could not find home directory").exit();
        }
    };
    let dir_path: PathBuf = [home_dir.as_str(), KEYSTORE_DEFAULT_FOLDER, chain_name]
        .iter()
        .collect();
    println!("dir_path {:?}", dir_path);
    if let Ok(dir) = fs::read_dir(dir_path) {
        println!("dir {:?}", dir);
        let ext = OsStr::new(KEYSTORE_FILE_EXTENSION);
        dir.into_iter()
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.extension() == Some(ext))
            .filter_map(|path| path.file_stem().map(OsStr::to_owned))
            .filter_map(|stem| stem.to_str().map(ToString::to_string))
            .next()
    } else {
        None
    }
}

/// Encapsulates the `hermes config auto` subcommand for generating
/// a default Hermes configuration.
#[derive(Clone, Command, Debug, Parser, PartialEq)]
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
        help_heading = "REQUIRED",
        help = "Key names to include in the config. Must provide keys for every chain."
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
        match runtime.block_on(get_configs(&sorted_chains, sorted_keys)) {
            Ok(mut chain_configs) => {
                if self.keys.is_none() {
                    let mut not_found = Vec::with_capacity(chain_configs.len());
                    for mut chain_config in chain_configs.iter_mut() {
                        let chain_id = &chain_config.id;
                        let key = find_key(chain_id.as_str());
                        if let Some(key) = key {
                            chain_config.key_name = key;
                        } else {
                            not_found.push(chain_id.as_str());
                        }
                    }
                    if !not_found.is_empty() {
                        Output::error(format!("No key found for chains {:?}", not_found)).exit();
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
