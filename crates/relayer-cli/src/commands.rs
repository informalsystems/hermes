//! Definition of all the Hermes subcommands

mod clear;
mod completions;
mod config;
mod create;
mod fee;
mod health;
mod keys;
mod listen;
mod misbehaviour;
mod query;
mod start;
mod tx;
mod update;
mod upgrade;
mod version;

use self::{
    clear::ClearCmds, completions::CompletionsCmd, config::ConfigCmd, create::CreateCmds,
    fee::FeeCmd, health::HealthCheckCmd, keys::KeysCmd, listen::ListenCmd,
    misbehaviour::MisbehaviourCmd, query::QueryCmd, start::StartCmd, tx::TxCmd, update::UpdateCmds,
    upgrade::UpgradeCmds, version::VersionCmd,
};

use core::time::Duration;
use std::path::PathBuf;

use abscissa_core::clap::Parser;
use abscissa_core::{config::Override, Command, Configurable, FrameworkError, Runnable};
use tracing::{error, info};

use crate::DEFAULT_CONFIG_PATH;
use ibc_relayer::config::Config;

/// Default configuration file path
pub fn default_config_file() -> Option<PathBuf> {
    dirs_next::home_dir().map(|home| home.join(DEFAULT_CONFIG_PATH))
}

/// Cli Subcommands
#[derive(Command, Parser, Debug, Runnable)]
pub enum CliCmd {
    /// Validate Hermes configuration file
    #[clap(subcommand)]
    Config(ConfigCmd),

    /// Manage keys in the relayer for each chain
    #[clap(subcommand)]
    Keys(KeysCmd),

    /// Create objects (client, connection, or channel) on chains
    #[clap(subcommand)]
    Create(CreateCmds),

    /// Update objects (clients) on chains
    #[clap(subcommand)]
    Update(UpdateCmds),

    /// Upgrade objects (clients) after chain upgrade
    #[clap(subcommand)]
    Upgrade(UpgradeCmds),

    /// Clear objects, such as outstanding packets on a channel.
    #[clap(subcommand)]
    Clear(ClearCmds),

    /// Start the relayer in multi-chain mode.
    ///
    /// Relays packets and open handshake messages between all chains in the config.
    Start(StartCmd),

    /// Query objects from the chain
    #[clap(subcommand)]
    Query(QueryCmd),

    /// Create and send IBC transactions
    #[clap(subcommand)]
    Tx(TxCmd),

    /// Interact with the fee middleware
    #[clap(subcommand)]
    Fee(FeeCmd),

    /// Listen to and display IBC events emitted by a chain
    Listen(ListenCmd),

    /// Listen to client update IBC events and handles misbehaviour
    Misbehaviour(MisbehaviourCmd),

    /// The `version` subcommand, retained for backward compatibility.
    Version(VersionCmd),

    /// Performs a health check of all chains in the the config
    HealthCheck(HealthCheckCmd),

    /// Generate auto-complete scripts for different shells.
    #[clap(display_order = 1000)]
    Completions(CompletionsCmd),
}

/// This trait allows you to define how application configuration is loaded.
impl Configurable<Config> for CliCmd {
    /// Location of the configuration file
    /// This is called only when the `-c` command-line option is omitted.
    fn config_path(&self) -> Option<PathBuf> {
        let path = default_config_file();

        match path {
            Some(path) if path.exists() => {
                info!("using default configuration from '{}'", path.display());
                Some(path)
            }
            Some(path) => {
                // No file exists at the config path
                error!("could not find configuration file at '{}'", path.display());
                error!("for an example, please see https://hermes.informal.systems/config.html#example-configuration-file");
                None
            }
            None => {
                // The path to the default config file could not be found
                error!("could not find default configuration file");
                error!(
                    "please create one at '~/{}' or specify it with the '-c'/'--config' flag",
                    DEFAULT_CONFIG_PATH
                );
                error!("for an example, please see https://hermes.informal.systems/config.html#example-configuration-file");
                None
            }
        }
    }

    /// Apply changes to the config after it's been loaded, e.g. overriding
    /// values in a config file using command-line options.
    ///
    /// This can be safely deleted if you don't want to override config
    /// settings from command-line options.
    fn process_config(&self, mut config: Config) -> Result<Config, FrameworkError> {
        // Alter the memo for all chains to include a suffix with Hermes build details
        let web = "https://hermes.informal.systems";
        let suffix = format!("{} {} ({})", CliCmd::name(), clap::crate_version!(), web);
        for ccfg in config.chains.iter_mut() {
            ccfg.memo_prefix.apply_suffix(&suffix);
        }

        // For all commands except for `start` Hermes retries
        // for a prolonged period of time.
        if !matches!(self, CliCmd::Start(_)) {
            for c in config.chains.iter_mut() {
                c.rpc_timeout = Duration::from_secs(120);
            }
        }

        match self {
            CliCmd::Tx(cmd) => cmd.override_config(config),
            CliCmd::Fee(cmd) => cmd.override_config(config),
            // CliCmd::Help(cmd) => cmd.override_config(config),
            // CliCmd::Keys(cmd) => cmd.override_config(config),
            // CliCmd::Create(cmd) => cmd.override_config(config),
            // CliCmd::Update(cmd) => cmd.override_config(config),
            // CliCmd::Upgrade(cmd) => cmd.override_config(config),
            // CliCmd::Start(cmd) => cmd.override_config(config),
            // CliCmd::Query(cmd) => cmd.override_config(config),
            // CliCmd::Listen(cmd) => cmd.override_config(config),
            // CliCmd::Misbehaviour(cmd) => cmd.override_config(config),
            // CliCmd::Version(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
