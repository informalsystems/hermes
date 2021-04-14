//! `upgrade` subcommand

use abscissa_core::{Command, Help, Options, Runnable};

use crate::commands::tx::client::TxUpgradeClientCmd;

#[derive(Command, Debug, Options, Runnable)]
pub enum UpgradeCmds {
    /// Generic `help`
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// Subcommand for upgrading a `client`
    #[options(help = "Upgrade an IBC client")]
    Client(TxUpgradeClientCmd),
}
