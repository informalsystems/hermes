/*!
    Helper functions for modifying the Gaia chain config in TOML.

    Since we do not need to understand the full structure of the
    CosmosSDK config, we are updating the config as dynamic TOML
    values instead of serializing them into proper types.
*/

use core::time::Duration;
use eyre::{eyre, Report as Error};
use toml::Value;

/// Set the `rpc` field in the full node config.
pub fn set_rpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("rpc")
        .ok_or_else(|| eyre!("expect rpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into(),
        );

    Ok(())
}

pub fn set_grpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("grpc")
        .ok_or_else(|| eyre!("expect grpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("address".to_string(), format!("0.0.0.0:{}", port).into());

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
        .insert(
            "laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into(),
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

pub fn set_max_deposit_period(genesis: &mut serde_json::Value, period: &str) -> Result<(), Error> {
    let max_deposit_period = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| gov.get_mut("deposit_params"))
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

pub fn set_voting_period(genesis: &mut serde_json::Value, period: &str) -> Result<(), Error> {
    let voting_period = genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get_mut("gov"))
        .and_then(|gov| gov.get_mut("voting_params"))
        .and_then(|voting_params| voting_params.as_object_mut())
        .ok_or_else(|| eyre!("failed to update voting_period in genesis file"))?;

    voting_period
        .insert(
            "voting_period".to_owned(),
            serde_json::Value::String(period.to_string()),
        )
        .ok_or_else(|| eyre!("failed to update voting_period in genesis file"))?;

    Ok(())
}
