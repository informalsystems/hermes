//! `keys` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod add;
mod balance;
mod delete;
mod list;

/// `keys` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum KeysCmd {
    /// Adds key to a configured chain or restores a key to a configured chain using a mnemonic
    Add(add::KeysAddCmd),

    /// Delete key(s) from a configured chain
    Delete(delete::KeysDeleteCmd),

    /// List keys configured on a chain
    List(list::KeysListCmd),

    /// Query balance for a key from a configured chain. If no key is given, the key is retrieved from the configuration file.
    Balance(balance::KeyBalanceCmd),
}
