//! `query tx` subcommand

use abscissa_core::{Command, Options, Runnable};

mod events;

/// `query tx` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryTxCmd {
    /// The `query tx events` subcommand
    #[options(help = "Query the events emitted by transaction")]
    Events(events::QueryTxEventsCmd),
}
