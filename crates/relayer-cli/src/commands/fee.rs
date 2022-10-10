//! `fee` subcommand

use abscissa_core::clap::Parser;
use abscissa_core::{config::Override, Command, Runnable};
use ibc_relayer::config::Config;

use self::register_counterparty_payee::RegisterCounterpartyPayeeCmd;
use self::register_payee::RegisterPayeeCmd;
use self::transfer::FeeTransferCmd;

pub mod register_counterparty_payee;
pub mod register_payee;
pub mod transfer;

#[allow(clippy::large_enum_variant)]
#[derive(Command, Debug, Parser, Runnable)]
pub enum FeeCmd {
    /// Register a payee for a channel
    RegisterPayee(RegisterPayeeCmd),

    /// Register a counterparty payee for a channel
    RegisterCounterpartyPayee(RegisterCounterpartyPayeeCmd),

    /// Perform a token transfer supported with a fee
    Transfer(FeeTransferCmd),
}

impl Override<Config> for FeeCmd {
    fn override_config(&self, config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        match self {
            Self::Transfer(cmd) => cmd.override_config(config),
            _ => Ok(config),
        }
    }
}
