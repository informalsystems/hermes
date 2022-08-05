//! `config` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod auto;
mod validate;

/// `config` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum ConfigCmd {
    /// Validate the relayer configuration
    Validate(validate::ValidateCmd),

    /// Automatically generate a relayer configuration file
    Auto(auto::AutoCmd),
}
