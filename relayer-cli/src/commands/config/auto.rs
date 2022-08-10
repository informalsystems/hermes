use abscissa_core::{
    clap::Parser,
    {Command, Runnable},
};
use chain_registry::relayer_config::get_configs;

use crate::conclude::Output;

use ibc_relayer::config::{store, Config};

use std::path::PathBuf;
use tokio::runtime::Builder;
use tracing::warn;

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
        required = true,
        multiple = true,
        value_name = "KEY_CHAIN_1 KEY_CHAIN_2...",
        help_heading = "REQUIRED",
        help = "Key names to include in the config. Must provide keys for every chain."
    )]
    keys: Vec<String>,
}

impl Runnable for AutoCmd {
    fn run(&self) {
        // Assert that for every chain, a key name is provided
        if self.chain_names.len() != self.keys.len() {
            Output::error("Must provide a key name for every chain").exit();
        }
        let runtime = Builder::new_current_thread().enable_all().build().unwrap();

        // Sort chains and keys together
        let mut chain_key_tuples: Vec<(String, String)> = self
            .chain_names
            .iter()
            .cloned()
            .zip(self.keys.iter().cloned())
            .collect();

        chain_key_tuples.sort_by(|a, b| (a.0.cmp(&b.0)));
        let (sorted_chains, sorted_keys): (Vec<String>, Vec<String>) =
            chain_key_tuples.into_iter().unzip();

        // Fetch chain configs
        match runtime.block_on(get_configs(&sorted_chains, &sorted_keys)) {
            Ok(chain_configs) => {
                let config: Config = Config {
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
