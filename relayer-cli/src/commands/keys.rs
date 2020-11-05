//! `keys` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

mod restore;
mod add;

/// `keys` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum KeysCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `keys add` subcommand
    #[options(help = "adds a key to a configured chain")]
    Add(add::KeyAddCmd),

    /// The `keys restore` subcommand
    #[options(help = "restore a key to a configured chain using a mnemonic")]
    Restore(restore::KeyRestoreCmd),
}
