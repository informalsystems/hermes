//! `keys` subcommand
use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

mod add;
mod balance;
mod delete;
mod list;

/// `keys` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum KeysCmd {
    /// Add a key to a chain from its keyring file or restore a key using its mnemonic
    Add(add::KeysAddCmd),

    /// Delete key(s) from a configured chain
    Delete(delete::KeysDeleteCmd),

    /// List keys configured for a chain
    List(list::KeysListCmd),

    /// Query balance for a key from a configured chain. If no key is given, the key is retrieved from the configuration file.
    Balance(balance::KeyBalanceCmd),
}
