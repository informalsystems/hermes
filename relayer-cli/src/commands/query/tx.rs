//! `query tx` subcommand

use abscissa_core::{Clap, Command, Runnable};

mod events;

/// `query tx` subcommand
#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryTxCmd {
    /// The `query tx events` subcommand
    #[clap(about = "Query the events emitted by transaction")]
    Events(events::QueryTxEventsCmd),
}
