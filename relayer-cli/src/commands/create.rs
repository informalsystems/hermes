//! `create` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

use crate::commands::create::channel::CreateChannelCommand;
use crate::commands::create::connection::CreateConnectionCommand;
use crate::commands::create::client::CreateClientCommand;

mod channel;
mod connection;
mod client;

/// `create` subcommands
#[derive(Command, Debug, Options, Runnable)]
pub enum CreateCmds {
    /// Generic `help`
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// Subcommand for creating a `client`
    #[options(help = "Create a new IBC client")]
    Client(CreateClientCommand),

    /// Subcommand for creating a `connection`
    #[options(help = "Create a new connection between two chains")]
    Connection(CreateConnectionCommand),

    /// Subcommand for creating a `channel`
    #[options(help = "Create a new channel between two chains")]
    Channel(CreateChannelCommand),
}
