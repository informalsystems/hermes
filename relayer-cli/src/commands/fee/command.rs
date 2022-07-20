//! `keys` subcommand
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::commands::fee::register_payee::RegisterPayeeCmd;

#[derive(Command, Debug, Parser, Runnable)]
pub enum FeeCmd {
    RegisterPayee(RegisterPayeeCmd),
}
