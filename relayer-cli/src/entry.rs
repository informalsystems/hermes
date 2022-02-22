use std::path::PathBuf;
use std::process;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Configurable, FrameworkError, Runnable};
use clap::IntoApp;
use ibc_relayer::config::Config;

use crate::commands::CliCmd;

/// Entry point for Hermes CLI.
#[derive(Command, Debug, Parser)]
#[clap(author, about, version)]
pub struct EntryPoint {
    /// Path to the configuration file
    #[clap(short = 'c', long, help = "path to configuration file")]
    pub config: Option<PathBuf>,

    /// Toggle JSON output mode one verbosity setting
    #[clap(short = 'j', long, help = "enable JSON output")]
    pub json: bool,

    /// Subcommand to execute.
    ///
    /// The `command` option will delegate option parsing to the command type,
    /// starting at the first free argument.
    #[clap(subcommand)]
    pub command: Option<CliCmd>,
}

impl Runnable for EntryPoint {
    fn run(&self) {
        match &self.command {
            Some(cmd) => cmd.run(),
            None => {
                EntryPoint::command().print_help().unwrap();
                process::exit(0);
            }
        }
    }
}

impl Configurable<Config> for EntryPoint {
    /// Path to the command's configuration file
    fn config_path(&self) -> Option<PathBuf> {
        // Skip config processing for `completions`
        // and the legacy `version` subcommand.
        match &self.command {
            Some(CliCmd::Completions(_)) | Some(CliCmd::Version(_)) => {
                return None;
            }
            _ => {}
        }

        match &self.config {
            // Use explicit `-c`/`--config` argument if passed
            Some(cfg) => Some(cfg.clone()),

            // Otherwise defer to the toplevel command's config path logic
            None => self.command.as_ref().and_then(|cmd| cmd.config_path()),
        }
    }

    /// Process the configuration after it has been loaded, potentially
    /// modifying it or returning an error if options are incompatible
    fn process_config(&self, config: Config) -> Result<Config, FrameworkError> {
        match &self.command {
            Some(cmd) => cmd.process_config(config),
            None => Ok(config),
        }
    }
}
