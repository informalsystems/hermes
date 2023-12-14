#![allow(unused_qualifications)] // Fix for warning in `ValueEnum` generated code

//! Definition of the entrypoint for the Hermes CLI.

use std::{
    path::PathBuf,
    process,
};

use abscissa_core::{
    clap::Parser,
    Command,
    Configurable,
    FrameworkError,
    Runnable,
};
use clap::{
    IntoApp,
    ValueEnum,
};
use ibc_relayer::{
    config::Config,
    util::debug_section::DebugSection,
};

use crate::commands::CliCmd;

#[derive(Copy, Clone, Debug, ValueEnum)]
pub enum CliDebugSection {
    Rpc,
    Profiling,
    ProfilingJson,
}

impl From<CliDebugSection> for DebugSection {
    fn from(section: CliDebugSection) -> Self {
        match section {
            CliDebugSection::Rpc => DebugSection::Rpc,
            CliDebugSection::Profiling => DebugSection::Profiling,
            CliDebugSection::ProfilingJson => DebugSection::ProfilingJson,
        }
    }
}

/// Entry point for Hermes CLI.
#[derive(Command, Debug, Parser)]
#[clap(author, about, version)]
pub struct EntryPoint {
    /// Path to the configuration file
    #[clap(long = "config", help = "Path to configuration file")]
    pub config: Option<PathBuf>,

    /// Toggle JSON output mode one verbosity setting
    #[clap(long = "json", help = "Enable JSON output")]
    pub json: bool,

    /// Enable the given debug sections, separated by commas.
    #[clap(
        long = "debug",
        help = "Enable debug output for the given section(s), comma separated, can be repeated.",
        value_enum,
        value_delimiter = ','
    )]
    pub debug: Vec<CliDebugSection>,

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
            // Use explicit `--config` argument if passed
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
