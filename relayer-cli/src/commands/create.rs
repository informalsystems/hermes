//! `create` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::commands::create::channel::CreateChannelCommand;
use crate::commands::create::connection::CreateConnectionCommand;
use crate::commands::tx::client::TxCreateClientCmd;

mod channel;
mod connection;

/// `create` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum CreateCmds {
    /// Create a new IBC client
    Client(TxCreateClientCmd),

    /// Create a new connection between two chains
    Connection(CreateConnectionCommand),

    /// Create a new channel between two chains using a pre-existing connection.
    /// Alternatively, create a new client and a new connection underlying
    /// the new channel if a pre-existing connection is not provided.
    Channel(CreateChannelCommand),
}
