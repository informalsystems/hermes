//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod client;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// The `query client` subcommand
    #[options(help = "query client state")]
    State(client::QueryClientStateCmd),

    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),
}
