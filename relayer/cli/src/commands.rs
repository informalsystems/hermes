//! Cli Subcommands
//!
//! This is where you specify the subcommands of your application.
//!
//! See the `impl Configurable` below for how to specify the path to the
//! application's configuration file.

mod config;
mod light;
mod start;
mod version;

use self::{config::ConfigCmd, light::LightCmd, start::StartCmd, version::VersionCmd};

use crate::config::Config;
use abscissa_core::{Command, Configurable, FrameworkError, Help, Options, Runnable};
use std::path::PathBuf;

/// Cli Configuration Filename
pub const CONFIG_FILE: &str = "relayer.toml";

/// Cli Subcommands
#[derive(Command, Debug, Options, Runnable)]
pub enum CliCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `version` subcommand
    #[options(help = "display version information")]
    Version(VersionCmd),

    /// The `start` subcommand
    #[options(help = "start the relayer")]
    Start(StartCmd),

    /// The `config` subcommand
    #[options(help = "manipulate the relayer configuration")]
    Config(ConfigCmd),

    /// The `light` subcommand
    #[options(help = "basic functionality for managing the lite clients")]
    Light(LightCmd),
}

/// This trait allows you to define how application configuration is loaded.
impl Configurable<Config> for CliCmd {
    /// Location of the configuration file
    fn config_path(&self) -> Option<PathBuf> {
        // Check if the config file exists, and if it does not, ignore it.
        // If you'd like for a missing configuration file to be a hard error
        // instead, always return `Some(CONFIG_FILE)` here.
        let filename = PathBuf::from(CONFIG_FILE);

        if filename.exists() {
            Some(filename)
        } else {
            None
        }
    }

    /// Apply changes to the config after it's been loaded, e.g. overriding
    /// values in a config file using command-line options.
    ///
    /// This can be safely deleted if you don't want to override config
    /// settings from command-line options.
    fn process_config(&self, config: Config) -> Result<Config, FrameworkError> {
        match self {
            // CliCmd::Start(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
