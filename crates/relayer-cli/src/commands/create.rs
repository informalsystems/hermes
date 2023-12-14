//! `create` subcommand
use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

use crate::commands::{
    create::{
        channel::CreateChannelCommand,
        connection::CreateConnectionCommand,
    },
    tx::client::TxCreateClientCmd,
};

mod channel;
mod connection;

/// `create` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum CreateCmds {
    /// Create a new IBC client
    Client(TxCreateClientCmd),

    /// Create a new connection between two chains
    Connection(CreateConnectionCommand),

    /// Create a new channel between two chains.
    ///
    /// Can create a new channel using a pre-existing connection or
    /// alternatively, create a new client and a new connection underlying
    /// the new channel if a pre-existing connection is not provided.
    Channel(CreateChannelCommand),
}
