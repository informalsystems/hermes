//! `tx` subcommand
use crate::commands::tx::client::{TxCreateClientCmd, TxUpdateClientCmd};
use abscissa_core::{Command, Help, Options, Runnable};

mod client;
mod connection;

/// `tx` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum TxCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `tx raw` subcommand
    #[options(help = "tx raw")]
    Raw(TxRawCommands),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum TxRawCommands {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `tx raw conn-init` subcommand
    #[options(help = "tx raw conn-init")]
    ConnInit(connection::TxRawConnInitCmd),

    /// The `tx raw client-create` subcommand submits a MsgCreateClient in a transaction to a chain
    #[options(help = "tx raw create-client")]
    CreateClient(TxCreateClientCmd),

    /// The `tx raw client-update` subcommand submits a MsgUpdateClient in a transaction to a chain
    #[options(help = "tx raw update-client")]
    UpdateClient(TxUpdateClientCmd),
}
