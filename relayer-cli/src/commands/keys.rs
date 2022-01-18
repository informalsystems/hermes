//! `keys` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod add;
mod delete;
mod list;
mod restore;

/// `keys` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum KeysCmd {
    /// Adds a key to a configured chain
    Add(add::KeysAddCmd),

    /// Delete key(s) from a configured chain
    Delete(delete::KeysDeleteCmd),

    /// List keys configured on a chain
    List(list::KeysListCmd),

    /// Restore a key to a configured chain using a mnemonic
    Restore(restore::KeyRestoreCmd),
}
