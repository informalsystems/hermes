use core::str::FromStr;
use eyre::eyre;
use ibc_relayer_types::applications::transfer::amount::Amount;
use serde_json as json;
use serde_yaml as yaml;
use std::collections::HashMap;
use tracing::debug;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};
use crate::prelude::*;

pub fn query_balance(
    chain_id: &str,
    command_path: &str,
    rpc_listen_address: &str,
    wallet_id: &str,
    denom: &str,
) -> Result<Amount, Error> {
    // SDK v0.50 has removed the `--denom` flag from the `query bank balances` CLI.
    // It also changed the JSON output.
    match simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "query",
            "bank",
            "balances",
            wallet_id,
            "--denom",
            denom,
            "--output",
            "json",
        ],
    ) {
        Ok(output) => {
            let amount_str = json::from_str::<json::Value>(&output.stdout)
                .map_err(handle_generic_error)?
                .get("amount")
                .ok_or_else(|| eyre!("expected amount field"))?
                .as_str()
                .ok_or_else(|| eyre!("expected string field"))?
                .to_string();

            let amount = Amount::from_str(&amount_str).map_err(handle_generic_error)?;

            Ok(amount)
        }
        Err(_) => {
            let res = simple_exec(
                chain_id,
                command_path,
                &[
                    "--node",
                    rpc_listen_address,
                    "query",
                    "bank",
                    "balances",
                    wallet_id,
                    "--output",
                    "json",
                ],
            )?
            .stdout;
            let amounts_array =
                json::from_str::<json::Value>(&res).map_err(handle_generic_error)?;

            let balances = amounts_array
                .get("balances")
                .ok_or_else(|| eyre!("expected balances field"))?
                .as_array()
                .ok_or_else(|| eyre!("expected array field"))?;

            let amount_str = balances.iter().find(|a| {
                a.get("denom")
                    .ok_or_else(|| eyre!("expected denom field"))
                    .unwrap()
                    == denom
            });

            match amount_str {
                Some(amount_str) => {
                    let amount_str = amount_str
                        .get("amount")
                        .ok_or_else(|| eyre!("expected amount field"))?
                        .as_str()
                        .ok_or_else(|| eyre!("expected amount to be in string format"))?;

                    let amount = Amount::from_str(amount_str).map_err(handle_generic_error)?;

                    Ok(amount)
                }
                None => {
                    debug!(
                        "Denom `{denom}` not found when querying for balance, will return 0{denom}"
                    );
                    Ok(Amount::from_str("0").map_err(handle_generic_error)?)
                }
            }
        }
    }
}

pub fn query_namada_balance(
    chain_id: &str,
    _command_path: &str,
    home_path: &str,
    denom: &Denom,
    wallet_id: &str,
    rpc_listen_address: &str,
) -> Result<Amount, Error> {
    let output = simple_exec(
        chain_id,
        //command_path,
        "namadac",
        &[
            "--base-dir",
            home_path,
            "balance",
            "--owner",
            wallet_id,
            "--show-ibc-tokens",
            "--node",
            rpc_listen_address,
        ],
    )?;

    let words: Vec<&str> = output.stdout.split_whitespace().collect();
    let denom_hash = &format!("{}:", denom.hash_only());

    if let Some(derived_index) = words.iter().position(|&w| w.contains(denom_hash)) {
        if let Some(&amount_str) = words.get(derived_index + 1) {
            return Amount::from_str(amount_str).map_err(handle_generic_error);
        }
        Err(Error::generic(eyre!(
            "chain id is not 1 words after `{denom_hash}`: raw output `{}` split output `{words:#?}`",
            output.stdout
        )))
    } else {
        let denom_display_name = &format!("{}:", denom.display_name());
        if let Some(derived_index) = words.iter().position(|&w| w.contains(denom_display_name)) {
            if let Some(&amount_str) = words.get(derived_index + 1) {
                return Amount::from_str(amount_str).map_err(handle_generic_error);
            }
            Err(Error::generic(eyre!(
                "chain id is not 1 words after `{denom_display_name}`: raw output `{}` split output `{words:#?}`",
                output.stdout
            )))
        } else {
            debug!("Denom `{denom_display_name}` not found when querying for balance, will return 0{denom}");
            Ok(Amount::from_str("0").map_err(handle_generic_error)?)
        }
    }
}

/**
    Query for the transactions related to a wallet on `Chain`
    receiving token transfer from others.
*/
pub fn query_recipient_transactions(
    chain_id: &str,
    command_path: &str,
    rpc_listen_address: &str,
    recipient_address: &str,
) -> Result<json::Value, Error> {
    let res = match simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "query",
            "txs",
            "--events",
            &format!("transfer.recipient={recipient_address}"),
        ],
    ) {
        Ok(output) => output.stdout,
        // Cosmos SDK v0.50.1 changed the `query txs` CLI flag from `--events` to `--query`
        Err(_) => {
            simple_exec(
                chain_id,
                command_path,
                &[
                    "--node",
                    rpc_listen_address,
                    "query",
                    "txs",
                    "--query",
                    &format!("transfer.recipient='{recipient_address}'"),
                ],
            )?
            .stdout
        }
    };

    tracing::debug!("parsing tx result: {}", res);

    match json::from_str(&res) {
        Ok(res) => Ok(res),
        _ => {
            let value: yaml::Value = yaml::from_str(&res).map_err(handle_generic_error)?;
            Ok(yaml_to_json_value(value)?)
        }
    }
}

// Hack to convert yaml::Value to json::Value. Unfortunately there is
// no builtin conversion provided even though both Value types are
// essentially the same. We just convert the two types to and from
// strings as a shortcut.
//
// TODO: properly implement a common trait that is implemented by
// dynamic types like json::Value, yaml::Value, and toml::Value.
// That way we can write generic functions that work with any of
// the dynamic value types for testing purposes.
fn yaml_to_json_value(value: yaml::Value) -> Result<json::Value, Error> {
    let json_str = json::to_string(&value).map_err(handle_generic_error)?;

    let parsed = json::from_str(&json_str).map_err(handle_generic_error)?;

    Ok(parsed)
}

/// Query pending Cross Chain Queries
pub fn query_cross_chain_query(
    chain_id: &str,
    command_path: &str,
    rpc_listen_address: &str,
) -> Result<String, Error> {
    let res = simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "query",
            "interchainquery",
            "list-pending-queries",
            "--output",
            "json",
        ],
    )?
    .stdout;

    Ok(res)
}

/// Query authority account for a specific module
pub fn query_auth_module(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    module_name: &str,
) -> Result<String, Error> {
    let account = match simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "query",
            "auth",
            "module-account",
            module_name,
            "--output",
            "json",
        ],
    ) {
        Ok(output) => {
            let json_res: HashMap<String, serde_json::Value> =
                serde_json::from_str(&output.stdout).map_err(handle_generic_error)?;

            json_res
                .get("account")
                .ok_or_else(|| eyre!("expect `account` string field to be present in json result"))?
                .clone()
        }
        Err(e) => {
            debug!("CLI `query auth module-account` failed, will try with `query auth module-accounts`: {e}");
            let output = simple_exec(
                chain_id,
                command_path,
                &[
                    "--home",
                    home_path,
                    "--node",
                    rpc_listen_address,
                    "query",
                    "auth",
                    "module-accounts",
                    "--output",
                    "json",
                ],
            )?
            .stdout;
            let json_res: HashMap<String, serde_json::Value> =
                serde_json::from_str(&output).map_err(handle_generic_error)?;

            let accounts = json_res
                .get("accounts")
                .ok_or_else(|| {
                    eyre!("expect `accounts` string field to be present in json result")
                })?
                .as_array()
                .ok_or_else(|| eyre!("expected `accounts` to be an array"))?;

            accounts
                .iter()
                .find(|&account| {
                    if let Some(name) = account.get("name") {
                        name == module_name
                    } else {
                        false
                    }
                })
                .ok_or_else(|| {
                    eyre!("expected to find the account for the `{module_name}` module")
                })?
                .clone()
        }
    };

    // Depending on the version used the CLI `query auth module-account` will have a field `base_account` or
    // or a field `value` containing the address.
    let res = match account.get("base_account") {
        Some(base_account) => base_account
            .get("address")
            .ok_or_else(|| eyre!("expect `address` string field to be present in json result"))?
            .as_str()
            .ok_or_else(|| eyre!("failed to convert value to &str"))?,
        None => account
            .get("value")
            .ok_or_else(|| eyre!("expect `value` string field to be present in json result"))?
            .get("address")
            .ok_or_else(|| eyre!("expect `address` string field to be present in json result"))?
            .as_str()
            .ok_or_else(|| eyre!("failed to convert value to &str"))?,
    };

    Ok(res.to_owned())
}
