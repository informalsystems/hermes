/*!
    Helper functions for modifying the Gaia chain config in TOML.

    Since we do not need to understand the full structure of the
    CosmosSDK config, we are updating the config as dynamic TOML
    values instead of serializing them into proper types.
*/

use core::time::Duration;
use eyre::{eyre, Report as Error};
use toml::Value;
use tracing::debug;

/// Set the `rpc` field in the full node config.
pub fn set_rpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("rpc")
        .ok_or_else(|| eyre!("expect rpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("laddr".to_string(), format!("tcp://0.0.0.0:{port}").into());

    Ok(())
}

pub fn enable_grpc(config: &mut Value) -> Result<(), Error> {
    config
        .get_mut("grpc")
        .ok_or_else(|| eyre!("expect grpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("enable".to_string(), true.into());

    Ok(())
}

pub fn set_grpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("grpc")
        .ok_or_else(|| eyre!("expect grpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("address".to_string(), format!("0.0.0.0:{port}").into());

    Ok(())
}

pub fn disable_grpc_web(config: &mut Value) -> Result<(), Error> {
    if let Some(field) = config.get_mut("grpc-web") {
        field
            .as_table_mut()
            .ok_or_else(|| eyre!("expect object"))?
            .insert("enable".to_string(), false.into());
    }

    Ok(())
}

pub fn disable_api(config: &mut Value) -> Result<(), Error> {
    if let Some(field) = config.get_mut("api") {
        field
            .as_table_mut()
            .ok_or_else(|| eyre!("expect object"))?
            .insert("enable".to_string(), false.into());
    }

    Ok(())
}

/// Set the `p2p` field in the full node config.
pub fn set_p2p_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("p2p")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("laddr".to_string(), format!("tcp://0.0.0.0:{port}").into());

    Ok(())
}

/// Set the `pprof_laddr` field in the full node config.
pub fn set_pprof_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "pprof_laddr".to_string(),
            format!("tcp://0.0.0.0:{port}").into(),
        );

    Ok(())
}

pub fn set_mempool_version(config: &mut Value, version: &str) -> Result<(), Error> {
    config
        .get_mut("mempool")
        .ok_or_else(|| eyre!("expect mempool section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("version".to_string(), version.into());

    Ok(())
}

/// Set the `consensus.timeout_commit` field in the full node config.
pub fn set_timeout_commit(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config
        .get_mut("consensus")
        .ok_or_else(|| eyre!("expect consensus section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "timeout_commit".to_string(),
            format!("{}ms", duration.as_millis()).into(),
        );

    Ok(())
}

/// Set the `consensus.timeout_propose` field in the full node config.
pub fn set_timeout_propose(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config
        .get_mut("consensus")
        .ok_or_else(|| eyre!("expect consensus section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "timeout_propose".to_string(),
            format!("{}ms", duration.as_millis()).into(),
        );

    Ok(())
}

/// Set the `log_level` field in the full node config.
pub fn set_log_level(config: &mut Value, log_level: &str) -> Result<(), Error> {
    config
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("log_level".to_string(), log_level.into());

    Ok(())
}

pub fn set_minimum_gas_price(config: &mut Value, price: &str) -> Result<(), Error> {
    config
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("minimum-gas-prices".to_string(), price.into());

    Ok(())
}

pub fn set_mode(config: &mut Value, mode: &str) -> Result<(), Error> {
    config
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("mode".to_string(), mode.into());

    Ok(())
}

pub fn set_indexer(config: &mut Value, mode: &str) -> Result<(), Error> {
    config
        .get_mut("tx_index")
        .ok_or_else(|| eyre!("expect tx_index section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("indexer".to_string(), mode.into());

    Ok(())
}

pub fn set_max_deposit_period(genesis: &mut serde_json::Value, period: &str) -> Result<(), Error> {
    let max_deposit_period = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| get_mut_with_fallback(gov, "params", "deposit_params"))
        .and_then(|deposit_params| deposit_params.as_object_mut())
        .ok_or_else(|| eyre!("failed to update max_deposit_period in genesis file"))?;

    max_deposit_period
        .insert(
            "max_deposit_period".to_owned(),
            serde_json::Value::String(period.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update max_deposit_period in genesis file"))?;

    Ok(())
}

pub fn set_min_deposit_amount(
    genesis: &mut serde_json::Value,
    min_deposit_amount: u64,
) -> Result<(), Error> {
    let min_deposit = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| get_mut_with_fallback(gov, "params", "deposit_params"))
        .and_then(|deposit_params| deposit_params.get_mut("min_deposit"))
        .and_then(|min_deposit| min_deposit.as_array_mut())
        .ok_or_else(|| eyre!("failed to find min_deposit in genesis file"))?
        .get_mut(0)
        .and_then(|min_deposit_entry| min_deposit_entry.as_object_mut())
        .ok_or_else(|| eyre!("failed to find first entry of min_deposit in genesis file"))?;

    min_deposit
        .insert(
            "amount".to_owned(),
            serde_json::Value::String(min_deposit_amount.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update deposit_params amount in genesis file"))?;

    Ok(())
}

pub fn set_staking_bond_denom(genesis: &mut serde_json::Value, denom: &str) -> Result<(), Error> {
    let bond_denom = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("staking"))
        .and_then(|staking| staking.get_mut("params"))
        .and_then(|params| params.as_object_mut())
        .ok_or_else(|| eyre!("failed to update bond_denom in genesis file"))?;

    bond_denom
        .insert(
            "bond_denom".to_owned(),
            serde_json::Value::String(denom.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update bond_denom in genesis file"))?;

    Ok(())
}

pub fn set_staking_max_entries(
    genesis: &mut serde_json::Value,
    entries: &str,
) -> Result<(), Error> {
    let max_entries = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("staking"))
        .and_then(|staking| staking.get_mut("params"))
        .and_then(|params| params.as_object_mut())
        .ok_or_else(|| eyre!("failed to update max_entries in genesis file"))?;

    max_entries
        .insert(
            "max_entries".to_owned(),
            serde_json::Value::String(entries.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update max_entries in genesis file"))?;

    Ok(())
}

pub fn set_mint_mint_denom(genesis: &mut serde_json::Value, denom: &str) -> Result<(), Error> {
    let mint_denom = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("mint"))
        .and_then(|mint| mint.get_mut("params"))
        .and_then(|params| params.as_object_mut())
        .ok_or_else(|| eyre!("failed to update mint_denom in genesis file"))?;

    mint_denom
        .insert(
            "mint_denom".to_owned(),
            serde_json::Value::String(denom.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update mint_denom in genesis file"))?;

    Ok(())
}

pub fn set_crisis_denom(genesis: &mut serde_json::Value, crisis_denom: &str) -> Result<(), Error> {
    let denom = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("crisis"))
        .and_then(|crisis| crisis.get_mut("constant_fee"))
        .and_then(|constant_fee| constant_fee.as_object_mut())
        .ok_or_else(|| eyre!("failed to update denom in genesis file"))?;

    denom
        .insert(
            "denom".to_owned(),
            serde_json::Value::String(crisis_denom.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update denom in genesis file"))?;

    Ok(())
}

pub fn set_voting_period(genesis: &mut serde_json::Value, period: u64) -> Result<(), Error> {
    // Expedited voting period must be strictly less that the regular voting period
    let regular_period = format!("{period}s");
    let expedited_period = format!("{}s", period - 1);
    let voting_period = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| get_mut_with_fallback(gov, "params", "voting_params"))
        .and_then(|voting_params| voting_params.as_object_mut())
        .ok_or_else(|| eyre!("failed to get voting_params in genesis file"))?;

    voting_period
        .insert(
            "voting_period".to_owned(),
            serde_json::Value::String(regular_period),
        )
        .ok_or_else(|| eyre!("failed to update voting_period in genesis file"))?;

    let maybe_expedited_voting_period = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| get_mut_with_fallback(gov, "params", "expedited_voting_period"));

    if let Some(expedited_voting_period) = maybe_expedited_voting_period {
        let expedited_voting_period = expedited_voting_period
            .as_object_mut()
            .ok_or_else(|| eyre!("failed to get voting_params in genesis file"))?;

        // Only insert `expedited_voting_period` if it already exists in order to avoid adding an unknown configuration in
        // chains using Cosmos SDK pre v0.50
        match expedited_voting_period.get("expedited_voting_period") {
            Some(_) => {
                expedited_voting_period
                .insert(
                    "expedited_voting_period".to_owned(),
                    serde_json::Value::String(expedited_period),
                ).ok_or_else(|| eyre!("failed to update expedited_voting_period in genesis file"))?;
            },
            None => debug!("`expedited_voting_period` was not updated, this configuration was introduced in Cosmos SDK v0.50"),
        }
    }

    Ok(())
}

pub fn set_soft_opt_out_threshold(
    genesis: &mut serde_json::Value,
    threshold: &str,
) -> Result<(), Error> {
    let params = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("ccvconsumer"))
        .and_then(|ccvconsumer| ccvconsumer.get_mut("params"))
        .and_then(|params| params.as_object_mut())
        .ok_or_else(|| eyre!("failed to get ccvconsumer params in genesis file"))?;

    // Might be none if the entry `soft_opt_out_threshold` didn't exist
    params.insert(
        "soft_opt_out_threshold".to_owned(),
        serde_json::Value::String(threshold.to_string()),
    );

    Ok(())
}

pub fn consensus_params_max_gas(
    genesis: &mut serde_json::Value,
    max_gas: &str,
) -> Result<(), Error> {
    let block = genesis
        .get_mut("consensus_params")
        .and_then(|consensus_params| consensus_params.get_mut("block"))
        .and_then(|block| block.as_object_mut())
        .ok_or_else(|| eyre!("failed to get `block` field in genesis file"))?;

    block.insert(
        "max_gas".to_owned(),
        serde_json::Value::String(max_gas.to_string()),
    );

    Ok(())
}

pub fn globalfee_minimum_gas_prices(
    genesis: &mut serde_json::Value,
    minimum_gas_prices: serde_json::Value,
) -> Result<(), Error> {
    let globalfee = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("globalfee"));

    // Only update `minimum_gas_prices` if `globalfee` is enabled
    match globalfee {
        Some(globalfee) => {
            let params = globalfee
                .get_mut("params")
                .and_then(|params| params.as_object_mut())
                .ok_or_else(|| eyre!("failed to get `params` fields in genesis file"))?;

            params.insert("minimum_gas_prices".to_owned(), minimum_gas_prices);
        }
        None => debug!("chain doesn't have `globalfee`"),
    }

    Ok(())
}

/// Look up a key in a JSON object, falling back to the second key if the first one cannot be found.
///
/// This lets us support both Tendermint 0.34 and 0.37, which sometimes use different keys for the
/// same configuration object in the genesis file.
///
/// Eg. in 0.34, the voting params are at `app_state.gov.voting_params`,
/// but in 0.37 they are at `app_state.gov.params`.
///
/// Note: This function is needed to avoid having to inline its code every time we need it.
/// The more obvious way to write it inline would be:
///
/// value.get_mut(key_034).or_else(|| value.get_mut(key_037))
///
/// but that does not work because of the first `get_mut` borrows `value` mutably, which
/// prevents the second `get_mut` from borrowing it again.
fn get_mut_with_fallback<'a>(
    value: &'a mut serde_json::Value,
    key: &str,
    fallback_key: &str,
) -> Option<&'a mut serde_json::Value> {
    let key = match value.get(key) {
        Some(value) if !value.is_null() => key,
        _ => fallback_key,
    };
    value.get_mut(key)
}
