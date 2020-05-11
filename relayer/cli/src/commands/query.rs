//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod channel;
mod client;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),
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
    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel ends` subcommand
    #[options(help = "query channel ends")]
    Ends(channel::QueryChannelEndsCmd),
}
