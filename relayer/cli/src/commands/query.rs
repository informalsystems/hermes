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
    /// The `query channel` subcommand
    #[options(help = "query channel")]
    Channel(QueryChannelCmds),

    /// The `query connection` subcommand
    #[options(help = "query connection")]
    Connection(QueryConnectionCmds),
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
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel ends` subcommand
    #[options(help = "query channel ends")]
    Ends(channel::QueryChannelEndsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection end` subcommand
    #[options(help = "query connection end")]
    End(connection::QueryConnectionEndCmd),
}

