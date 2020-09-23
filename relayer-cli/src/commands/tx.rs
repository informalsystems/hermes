//! `tx` subcommand

use crate::commands::tx::client::TxCreateClientCmd;
use abscissa_core::{Command, Options, Runnable};

mod client;

/// `tx` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum TxCmd {
    /// The `tx raw` subcommand
    #[options(help = "tx raw")]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum TxRawCommands {
    /// The `tx raw client-create` subcommand
    #[options(help = "tx raw create-client")]
    CreateClient(TxCreateClientCmd),
}
