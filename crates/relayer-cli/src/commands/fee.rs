//! `fee` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use register_counterparty_payee::RegisterCounterpartyPayeeCmd;
use register_payee::RegisterPayeeCmd;

pub mod register_counterparty_payee;
pub mod register_payee;

#[derive(Command, Debug, Parser, Runnable)]
pub enum FeeCmd {
    /// Register a payee for a channel
    RegisterPayee(RegisterPayeeCmd),

    /// Register a counterparty payee for a channel
    RegisterCounterpartyPayee(RegisterCounterpartyPayeeCmd),
}
