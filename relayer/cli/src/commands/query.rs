//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

mod query;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query clients` subcommand
    #[options(help = "IBC query to a full node")]
    Clients(query::QueryClientsCmd),
}
