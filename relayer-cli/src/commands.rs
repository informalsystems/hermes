//! Cli Subcommands
//!
//! This is where you specify the subcommands of your application.
//!
//! See the `impl Configurable` below for how to specify the path to the
//! application's configuration file.

use std::path::PathBuf;

use abscissa_core::{Command, Configurable, FrameworkError, Help, Options, Runnable};

use crate::commands::channel::ChannelCmds;
use crate::config::Config;

use self::{
    keys::KeysCmd, light::LightCmd, listen::ListenCmd, query::QueryCmd, start::StartCmd, tx::TxCmd,
    version::VersionCmd,
};

mod channel;
mod cli_utils;
mod config;
mod keys;
mod light;
mod listen;
mod query;
mod start;
mod tx;
mod version;

/// Default configuration file path
pub fn default_config_file() -> Option<PathBuf> {
    dirs_next::home_dir().map(|home| home.join(".hermes/config.toml"))
}

// TODO: Re-add the `config` subcommand
// /// The `config` subcommand
// #[options(help = "manipulate the relayer configuration")]
// Config(ConfigCmd),

/// Cli Subcommands
#[derive(Command, Debug, Options, Runnable)]
pub enum CliCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `start` subcommand
    #[options(help = "start the relayer (currently this refers to the v0 relayer)")]
    Start(StartCmd),

    /// The `channel` subcommand
    #[options(help = "channel functionality for managing channels")]
    Channel(ChannelCmds),

    /// The `listen` subcommand
    #[options(help = "listen to IBC events")]
    Listen(ListenCmd),

    /// The `version` subcommand
    #[options(help = "display version information")]
    Version(VersionCmd),

    /// The `query` subcommand
    #[options(help = "query state from chain")]
    Query(QueryCmd),

    /// The `tx` subcommand
    #[options(help = "create IBC transactions on configured chains")]
    Tx(TxCmd),

    /// The `light` subcommand
    #[options(help = "basic functionality for managing the lite clients")]
    Light(LightCmd),

    /// The `keys` subcommand
    #[options(help = "manage keys in the relayer for each chain")]
    Keys(KeysCmd),
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
        Ok(config)
    }
}
