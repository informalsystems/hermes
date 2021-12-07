//! `keys` subcommand
use abscissa_core::{Clap, Command, Runnable};

mod add;
mod delete;
mod list;
mod restore;

/// `keys` subcommand
#[derive(Command, Debug, Clap, Runnable)]
pub enum KeysCmd {
    /// The `keys add` subcommand
    #[clap(about = "Adds a key to a configured chain")]
    Add(add::KeysAddCmd),

    /// The `keys delete` subcommand
    #[clap(about = "Delete key(s) from a configured chain")]
    Delete(delete::KeysDeleteCmd),

    /// The `keys list` subcommand
    #[clap(about = "List keys configured on a chain")]
    List(list::KeysListCmd),

    /// The `keys restore` subcommand
    #[clap(about = "restore a key to a configured chain using a mnemonic")]
    Restore(restore::KeyRestoreCmd),
}
