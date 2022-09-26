//! `upgrade` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::commands::tx::client::{TxUpgradeClientCmd, TxUpgradeClientsCmd};

#[derive(Command, Debug, Parser, Runnable)]
pub enum UpgradeCmds {
    /// Upgrade an IBC client
    Client(TxUpgradeClientCmd),

    /// Upgrade all IBC clients that target a specific chain
    Clients(TxUpgradeClientsCmd),
}
