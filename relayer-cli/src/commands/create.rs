//! `create` subcommand
use abscissa_core::{Command, Help, Options, Runnable};

use crate::commands::create::connection::CreateConnectionCommand;

mod channel;
mod connection;

/// `create` subcommands
#[derive(Command, Debug, Options, Runnable)]
pub enum CreateCmds {
    /// Generic `help`
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// Subcommand for creating a `connection`
    #[options(help = "create a new connection between two chains")]
    Connection(CreateConnectionCommand),

    // /// Subcommand for creating a `channel` with various
    // #[options(help = "create a new channel between two chains")]
    // Channel(CreateChannelCommand),
}

