//! Cli Subcommands
//!
//! This is where you specify the subcommands of your application.
//!
//! See the `impl Configurable` below for how to specify the path to the
//! application's configuration file.

use std::path::PathBuf;

use abscissa_core::{config::Override, Clap, Command, Configurable, FrameworkError, Runnable};
use clap::IntoApp;
use tracing::{error, info};

use crate::DEFAULT_CONFIG_PATH;
use ibc_relayer::config::Config;

use self::{
    config::ConfigCmd, create::CreateCmds, health::HealthCheckCmd, keys::KeysCmd,
    listen::ListenCmd, misbehaviour::MisbehaviourCmd, query::QueryCmd, start::StartCmd, tx::TxCmd,
    update::UpdateCmds, upgrade::UpgradeCmds,
};

mod config;
mod create;
mod health;
mod keys;
mod listen;
mod misbehaviour;
mod query;
mod start;
mod tx;
mod update;
mod upgrade;

/// Default configuration file path
pub fn default_config_file() -> Option<PathBuf> {
    dirs_next::home_dir().map(|home| home.join(DEFAULT_CONFIG_PATH))
}

/// Cli Subcommands
#[derive(Command, Clap, Debug, Runnable)]
pub enum CliCmd {
    /// The `config` subcommand
    #[clap(subcommand, about = "Validate Hermes configuration file")]
    Config(ConfigCmd),

    /// The `keys` subcommand
    #[clap(subcommand, about = "Manage keys in the relayer for each chain")]
    Keys(KeysCmd),

    /// The `create` subcommand
    #[clap(
        subcommand,
        about = "Create objects (client, connection, or channel) on chains"
    )]
    Create(CreateCmds),

    /// The `update` subcommand
    #[clap(subcommand, about = "Update objects (clients) on chains")]
    Update(UpdateCmds),

    /// The `upgrade` subcommand
    #[clap(subcommand, about = "Upgrade objects (clients) after chain upgrade")]
    Upgrade(UpgradeCmds),

    /// The `start` subcommand
    #[clap(about = "Start the relayer in multi-chain mode. \
                      Relays packets and open handshake messages between all chains in the config.")]
    Start(StartCmd),

    /// The `query` subcommand
    #[clap(subcommand, about = "Query objects from the chain")]
    Query(QueryCmd),

    /// The `tx` subcommand
    #[clap(subcommand, about = "Create and send IBC transactions")]
    Tx(TxCmd),

    /// The `listen` subcommand
    #[clap(about = "Listen to and display IBC events emitted by a chain")]
    Listen(ListenCmd),

    /// The `misbehaviour` subcommand
    #[clap(about = "Listen to client update IBC events and handles misbehaviour")]
    Misbehaviour(MisbehaviourCmd),

    /// The `health` subcommand
    #[clap(about = "Performs a health check of all chains in the the config")]
    HealthCheck(HealthCheckCmd),
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
        let app = CliCmd::into_app();
        let web = "https://hermes.informal.systems";
        let suffix = format!("{} {} ({})", app.get_name(), app.render_long_version(), web);
        for ccfg in config.chains.iter_mut() {
            ccfg.memo_prefix.apply_suffix(&suffix);
        }

        match self {
            CliCmd::Tx(cmd) => cmd.override_config(config),
            // CliCmd::Help(cmd) => cmd.override_config(config),
            // CliCmd::Keys(cmd) => cmd.override_config(config),
            // CliCmd::Create(cmd) => cmd.override_config(config),
            // CliCmd::Update(cmd) => cmd.override_config(config),
            // CliCmd::Upgrade(cmd) => cmd.override_config(config),
            // CliCmd::Start(cmd) => cmd.override_config(config),
            // CliCmd::StartMulti(cmd) => cmd.override_config(config),
            // CliCmd::Query(cmd) => cmd.override_config(config),
            // CliCmd::Listen(cmd) => cmd.override_config(config),
            // CliCmd::Misbehaviour(cmd) => cmd.override_config(config),
            // CliCmd::Version(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
