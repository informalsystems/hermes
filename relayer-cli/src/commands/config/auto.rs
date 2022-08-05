use std::path::PathBuf;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use chain_registry::{error::RegistryError, relayer_config::hermes_config};

use crate::conclude::Output;

use futures::{stream::FuturesUnordered, StreamExt};

use ibc_relayer::config::{store, ChainConfig, Config};

use tokio::runtime::Builder;

#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct AutoCmd {
    #[clap(
        long = "path",
        short = 'p',
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
        value_name = "CHAIN_NAME1 CHAIN_NAME2...",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to include in the config"
    )]
    chain_ids: Vec<String>,

    #[clap(
        long = "key-names",
        required = true,
        multiple = true,
        value_name = "KEY_NAME_CHAIN1 KEY_NAME_CHAIN2...",
        help_heading = "REQUIRED",
        help = "key names to include in the config"
    )]
    key_names: Vec<String>,
}

async fn get_chain_configs(
    chain_names: &[String],
    key_names: &[String],
) -> Vec<Result<ChainConfig, RegistryError>> {
    let futures = FuturesUnordered::new();
    chain_names
        .iter()
        .zip(key_names.iter())
        .for_each(|(chain_name, key_name)| {
            futures.push(hermes_config(chain_name.as_str(), key_name.as_str()));
        });

    futures
        .collect::<Vec<Result<ChainConfig, RegistryError>>>()
        .await
}

impl Runnable for AutoCmd {
    fn run(&self) {
        // Assert that for every chain, a key name is provided
        if self.chain_ids.len() != self.key_names.len() {
            Output::error("Must provide a key name for every chain").exit();
        }
        let runtime = Builder::new_multi_thread()
            .worker_threads(1)
            .enable_all()
            .build()
            .unwrap();

        let chain_configs: Vec<ChainConfig> = runtime
            .block_on(get_chain_configs(&self.chain_ids, &self.key_names))
            .into_iter()
            .map(|result| match result {
                Ok(chain_config) => chain_config,
                Err(e) => Output::error(e.to_string()).exit(),
            })
            .collect();

        let config: Config = Config {
            chains: chain_configs,
            ..Config::default()
        };

        if let Err(e) = store(&config, &self.path) {
            Output::error(e.to_string()).exit();
        }
    }
}
