use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, json, Output};

/// The data structure that represents the arguments when invoking the `keys balance` CLI command.
///
/// The command must be invoked with the arguments in this order:
///
/// `keys balance <chain_id> <keyname>
///
/// If successful the balance and denominator of the account, associated with the given keyname
/// on the given chain, will be displayed.
#[derive(Clone, Command, Debug, Parser)]
pub struct KeyBalanceCmd {
    #[clap(required = true, help = "identifier of the chain")]
    chain_id: ChainId,

    #[clap(required = true, help = "name of the key")]
    key_name: String,
}

impl Runnable for KeyBalanceCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);
        let key_name = self.key_name.clone();

        match chain.query_balance(Some(key_name)) {
            Ok(balance) if json() => Output::success(balance).exit(),
            Ok(balance) => {
                Output::success_msg(format!("balance {} {}", balance.amount, balance.denom)).exit()
            }
            Err(e) => Output::error(format!(
                "there was a problem querying the chain balance: {}",
                e
            ))
            .exit(),
        }
    }
}
