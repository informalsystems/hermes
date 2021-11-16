//! `update` subcommand

use abscissa_core::{Clap, Command, Runnable};

use crate::commands::tx::client::TxUpdateClientCmd;

#[derive(Command, Debug, Clap, Runnable)]
pub enum UpdateCmds {
    /// Subcommand for updating a `client`
    #[clap(about = "Update an IBC client")]
    Client(TxUpdateClientCmd),
}
