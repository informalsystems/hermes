//! `query transfer` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod denom_trace;

/// `query transfer` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum TransferCmd {
    /// Query the denomination trace info from a trace hash
    DenomTrace(denom_trace::DenomTraceCmd),
}
