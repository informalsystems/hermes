//! `config` subcommand

use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

mod auto;
mod validate;

/// `config` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum ConfigCmd {
    /// Validate the relayer configuration
    Validate(validate::ValidateCmd),

    /// Automatically generate a config.toml for the specified chain(s)
    Auto(auto::AutoCmd),
}
