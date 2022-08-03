//! `config` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod validate;

/// `config` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum ConfigCmd {
    /// Validate the relayer configuration
    Validate(validate::ValidateCmd),

    /// Automatically generate a relayer configuration file
    #[clap(subcommand)]
    Automated(automated::AutomatedCmd),
}
