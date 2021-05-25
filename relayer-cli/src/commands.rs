//! Cli Subcommands
//!
//! This is where you specify the subcommands of your application.
//!
//! See the `impl Configurable` below for how to specify the path to the
//! application's configuration file.

use std::path::PathBuf;

use abscissa_core::{
    config::Override, Command, Configurable, FrameworkError, Help, Options, Runnable,
};
use tracing::info;

use crate::config::Config;
use crate::DEFAULT_CONFIG_PATH;

use self::{
    create::CreateCmds, keys::KeysCmd, listen::ListenCmd, query::QueryCmd, start::StartCmd,
    tx::TxCmd, update::UpdateCmds, upgrade::UpgradeCmds, version::VersionCmd,
};
use crate::commands::misbehaviour::MisbehaviourCmd;

mod config;
mod create;
mod keys;
mod listen;
mod misbehaviour;
mod query;
mod start;
mod tx;
mod update;
mod upgrade;
mod version;

/// Default configuration file path
pub fn default_config_file() -> Option<PathBuf> {
    info!("Using default configuration from: '.hermes/config.toml'");
    dirs_next::home_dir().map(|home| home.join(DEFAULT_CONFIG_PATH))
}

// TODO: Re-add the `config` subcommand
// /// The `config` subcommand
// #[options(help = "manipulate the relayer configuration")]
// Config(ConfigCmd),

/// Cli Subcommands
#[derive(Command, Debug, Options, Runnable)]
pub enum CliCmd {
    /// The `help` subcommand
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// The `keys` subcommand
    #[options(help = "Manage keys in the relayer for each chain")]
    Keys(KeysCmd),

    /// The `create` subcommand
    #[options(help = "Create objects (client, connection, or channel) on chains")]
    Create(CreateCmds),

    /// The `update` subcommand
    #[options(help = "Update objects (clients) on chains")]
    Update(UpdateCmds),

    /// The `upgrade` subcommand
    #[options(help = "Upgrade objects (clients) after chain upgrade")]
    Upgrade(UpgradeCmds),

    /// The `start` subcommand
    #[options(help = "Start the relayer in multi-chain mode. \
                      Handles packet relaying across all open channels between all chains in the config.")]
    Start(StartCmd),

    /// The `query` subcommand
    #[options(help = "Query objects from the chain")]
    Query(QueryCmd),

    /// The `tx` subcommand
    #[options(help = "Create and send IBC transactions")]
    Tx(TxCmd),

    /// The `listen` subcommand
    #[options(help = "Listen to and display IBC events emitted by a chain")]
    Listen(ListenCmd),

    /// The `misbehaviour` subcommand
    #[options(help = "Listen to client update IBC events and handles misbehaviour")]
    Misbehaviour(MisbehaviourCmd),

    /// The `version` subcommand
    #[options(help = "Display version information")]
    Version(VersionCmd),
}

/// This trait allows you to define how application configuration is loaded.
impl Configurable<Config> for CliCmd {
    /// Location of the configuration file
    fn config_path(&self) -> Option<PathBuf> {
        let filename = default_config_file();
        filename.filter(|f| f.exists())
    }

    /// Apply changes to the config after it's been loaded, e.g. overriding
    /// values in a config file using command-line options.
    ///
    /// This can be safely deleted if you don't want to override config
    /// settings from command-line options.
    fn process_config(&self, config: Config) -> Result<Config, FrameworkError> {
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
