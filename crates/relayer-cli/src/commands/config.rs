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

    ///Automatically generate a configuration file by fetching data from the chain-registry. If a pair of chains exists in the _IBC folder of the chain-registry then a corresponding packet filter is added to the configuration
    Auto(auto::AutoCmd),
}
