//! `config` subcommand

use abscissa_core::{Clap, Command, Runnable};

mod validate;

/// `config` subcommand
#[derive(Command, Debug, Clap, Runnable)]
pub enum ConfigCmd {
    /// The `config validate` subcommand
    #[clap(about = "validate the relayer configuration")]
    Validate(validate::ValidateCmd),
}
