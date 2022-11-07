use std::fmt::Write;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, json, Output};

/// The data structure that represents the arguments when invoking the `keys balance` CLI command.
///
/// The command has one argument and one optional flag:
///
/// `keys balance --chain <chain_id> --key-name <KEY_NAME>`
///
/// If no key name is given, it will be taken from the configuration file.
/// If successful the balance and denominator of the account, associated with the key name
/// on the given chain, will be displayed.
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct KeyBalanceCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "key-name",
        value_name = "KEY_NAME",
        help = "(optional) name of the key (defaults to the `key_name` defined in the config)"
    )]
    key_name: Option<String>,

    #[clap(
        long = "denom",
        value_name = "DENOM",
        help = "(optional) query the balance for the given denom (defaults to the `denom` defined in the config for the gas price)"
    )]
    denom: Option<String>,

    #[clap(
        long = "all",
        help = "(optional) query the balance for all denom. This flag overwrites the `--denom` flag (defaults to false)"
    )]
    all: bool,
}

impl Runnable for KeyBalanceCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let key_name = self.key_name.clone();

        if self.all {
            get_balances(chain, key_name)
        } else {
            get_balance(chain, key_name, self.denom.clone());
        }
    }
}

fn get_balance(chain: impl ChainHandle, key_name: Option<String>, denom: Option<String>) {
    match chain.query_balance(key_name.clone(), denom) {
        Ok(balance) if json() => Output::success(balance).exit(),
        Ok(balance) => {
            // Retrieve the key name string to output.
            let key_name = key_name.unwrap_or_else(|| {
                let chain_config = chain.config().unwrap_or_else(exit_with_unrecoverable_error);
                chain_config.key_name
            });

            Output::success_msg(format!(
                "balance for key `{}`: {} {}",
                key_name, balance.amount, balance.denom
            ))
            .exit()
        }
        Err(e) => Output::error(format!("there was a problem querying the balance: {}", e)).exit(),
    }
}

fn get_balances(chain: impl ChainHandle, key_name: Option<String>) {
    match chain.query_all_balances(key_name.clone()) {
        Ok(balances) if json() => Output::success(balances).exit(),
        Ok(balances) => {
            // Retrieve the key name string to output.
            let key_name = key_name.unwrap_or_else(|| {
                let chain_config = chain.config().unwrap_or_else(exit_with_unrecoverable_error);
                chain_config.key_name
            });

            let mut pretty_output = format!("Balances for key `{}`:", key_name);
            for balance in balances {
                write!(pretty_output, "\n\t{} {}", balance.amount, balance.denom)
                    .unwrap_or_else(exit_with_unrecoverable_error);
            }

            Output::success_msg(pretty_output).exit()
        }
        Err(e) => Output::error(format!("there was a problem querying the balance: {}", e)).exit(),
    }
}

#[cfg(test)]
mod tests {

    use super::KeyBalanceCmd;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_keys_balance_required_only() {
        assert_eq!(
            KeyBalanceCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: None,
                denom: None,
                all: false,
            },
            KeyBalanceCmd::parse_from(["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_keys_balance_name() {
        assert_eq!(
            KeyBalanceCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: Some("kname".to_owned()),
                denom: None,
                all: false,
            },
            KeyBalanceCmd::parse_from(["test", "--chain", "chain_id", "--key-name", "kname"])
        )
    }

    #[test]
    fn test_keys_balance_denom() {
        assert_eq!(
            KeyBalanceCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: None,
                denom: Some("samoleans".to_owned()),
                all: false,
            },
            KeyBalanceCmd::parse_from(["test", "--chain", "chain_id", "--denom", "samoleans"])
        )
    }

    #[test]
    fn test_keys_balance_all_denom() {
        assert_eq!(
            KeyBalanceCmd {
                chain_id: ChainId::from_string("chain_id"),
                key_name: None,
                denom: None,
                all: true,
            },
            KeyBalanceCmd::parse_from(["test", "--chain", "chain_id", "--all"])
        )
    }

    #[test]
    fn test_keys_balance_no_chain() {
        assert!(KeyBalanceCmd::try_parse_from(["test"]).is_err())
    }
}
