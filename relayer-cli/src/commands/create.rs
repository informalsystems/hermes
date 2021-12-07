//! `create` subcommand
use abscissa_core::{Clap, Command, Runnable};

use crate::commands::create::channel::CreateChannelCommand;
use crate::commands::create::connection::CreateConnectionCommand;
use crate::commands::tx::client::TxCreateClientCmd;

mod channel;
mod connection;

/// `create` subcommands
#[derive(Command, Debug, Clap, Runnable)]
pub enum CreateCmds {
    /// Subcommand for creating a `client`
    #[clap(about = "Create a new IBC client")]
    Client(TxCreateClientCmd),

    /// Subcommand for creating a `connection`
    #[clap(about = "Create a new connection between two chains")]
    Connection(CreateConnectionCommand),

    /// Subcommand for creating a `channel`
    #[clap(about = "Create a new channel between two chains")]
    Channel(CreateChannelCommand),
}
