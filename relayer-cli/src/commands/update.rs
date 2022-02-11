//! `update` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::commands::tx::client::TxUpdateClientCmd;

#[derive(Command, Debug, Parser, Runnable)]
pub enum UpdateCmds {
    /// Update an IBC client
    Client(TxUpdateClientCmd),
}
