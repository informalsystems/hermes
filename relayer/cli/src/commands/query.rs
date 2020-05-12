//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod client;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),

    /// The `query connection` subcommand
    #[options(help = "query connection")]
    Connection(QueryConnectionCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// The `query client` subcommand
    #[options(help = "query client state")]
    State(client::QueryClientStateCmd),

    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection` subcommand
    #[options(help = "query a connection")]
    Connection(client::QueryConnectionCmd),
}
