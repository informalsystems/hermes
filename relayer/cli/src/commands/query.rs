//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod channel;
mod client;
mod connection;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),

    /// The `query connection` subcommand
    #[options(help = "query connection")]
    Connection(QueryConnectionCmds),

    /// The `query channel` subcommand
    #[options(help = "query channel")]
    Channel(QueryChannelCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// The `query client state` subcommand
    #[options(help = "query client full state")]
    State(client::QueryClientStateCmd),
    /// The `query client consensus` subcommand

    /// The `query client consensus` subcommand
    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),

    /// The `query client connections` subcommand
    #[options(help = "query client connections")]
    Connections(client::QueryClientConnectionsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection end` subcommand
    #[options(help = "query connection end")]
    End(connection::QueryConnectionEndCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel end` subcommand
    #[options(help = "query channel end")]
    End(channel::QueryChannelEndCmd),
}
