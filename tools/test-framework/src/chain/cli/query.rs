use core::str::FromStr;
use eyre::eyre;
use serde_json as json;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

pub fn query_balance(
    chain_id: &str,
    command_path: &str,
    rpc_listen_address: &str,
    wallet_id: &str,
    denom: &str,
) -> Result<u128, Error> {
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

    let amount = u128::from_str(&amount_str).map_err(handle_generic_error)?;

    Ok(amount)
}
