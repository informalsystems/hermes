//! `keys` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

mod restore;

/// `keys` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum KeysCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `keys restore` subcommand
    #[options(help = "keys restore")]
    Restore(restore::KeyRestoreCmd),
}
