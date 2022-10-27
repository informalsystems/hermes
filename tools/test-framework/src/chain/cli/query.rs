use core::str::FromStr;
use eyre::eyre;
use ibc_relayer_types::applications::transfer::amount::Amount;
use serde_json as json;
use serde_yaml as yaml;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

pub fn query_balance(
    chain_id: &str,
    command_path: &str,
    rpc_listen_address: &str,
    wallet_id: &str,
    denom: &str,
) -> Result<Amount, Error> {
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
            "--denom",
            denom,
            "--output",
            "json",
        ],
    )?
    .stdout;

    let amount_str = json::from_str::<json::Value>(&res)
        .map_err(handle_generic_error)?
        .get("amount")
        .ok_or_else(|| eyre!("expected amount field"))?
        .as_str()
        .ok_or_else(|| eyre!("expected string field"))?
        .to_string();

    let amount = Amount::from_str(&amount_str).map_err(handle_generic_error)?;

    Ok(amount)
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
    let res = simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "query",
            "txs",
            "--events",
            &format!("transfer.recipient={}", recipient_address),
        ],
    )?
    .stdout;

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
