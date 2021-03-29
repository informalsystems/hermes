//! `update` subcommand

use abscissa_core::{Command, Help, Options, Runnable};

use crate::commands::tx::client::TxUpdateClientCmd;

#[derive(Command, Debug, Options, Runnable)]
pub enum UpdateCmds {
    /// Generic `help`
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// Subcommand for updating a `client`
    #[options(help = "Update an IBC client")]
    Client(TxUpdateClientCmd),
}
