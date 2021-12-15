//! `upgrade` subcommand

use abscissa_core::{Clap, Command, Runnable};

use crate::commands::tx::client::{TxUpgradeClientCmd, TxUpgradeClientsCmd};

#[derive(Command, Debug, Clap, Runnable)]
pub enum UpgradeCmds {
    /// Subcommand for upgrading a `client`
    #[clap(about = "Upgrade an IBC client")]
    Client(TxUpgradeClientCmd),

    /// Subcommand for upgrading all `client`s that target specified chain
    #[clap(about = "Upgrade all IBC clients that target a specific chain")]
    Clients(TxUpgradeClientsCmd),
}
