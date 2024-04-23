use eyre::{eyre, Report as Error};
use toml::Value;

/// Set the `rpc` field in the full node config.
pub fn set_rpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("ledger")
        .ok_or_else(|| eyre!("expect ledger section"))?
        .get_mut("cometbft")
        .ok_or_else(|| eyre!("expect cometbft section"))?
        .get_mut("rpc")
        .ok_or_else(|| eyre!("expect cometbft rpc"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into(),
        );

    Ok(())
}

/// Set the `p2p` field in the full node config.
pub fn set_p2p_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("ledger")
        .ok_or_else(|| eyre!("expect ledger section"))?
        .get_mut("cometbft")
        .ok_or_else(|| eyre!("expect cometbft section"))?
        .get_mut("p2p")
        .ok_or_else(|| eyre!("expect cometbft rpc"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into(),
        );

    Ok(())
}

/// Set the `p2p` field in the full node config.
pub fn set_proxy_app_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config
        .get_mut("ledger")
        .ok_or_else(|| eyre!("expect ledger section"))?
        .get_mut("cometbft")
        .ok_or_else(|| eyre!("expect cometbft section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "proxy_app".to_string(),
            format!("tcp://0.0.0.0:{}", port).into(),
        );

    Ok(())
}

pub fn set_unbonding_len(parameters: &mut Value, unbonding_len: i64) -> Result<(), Error> {
    parameters
        .get_mut("pos_params")
        .ok_or_else(|| eyre!("expect pos_params section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("unbonding_len".to_string(), Value::Integer(unbonding_len));

    Ok(())
}

pub fn set_pipeline_len(parameters: &mut Value, pipeline_len: i64) -> Result<(), Error> {
    parameters
        .get_mut("pos_params")
        .ok_or_else(|| eyre!("expect pos_params section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("pipeline_len".to_string(), Value::Integer(pipeline_len));

    Ok(())
}

pub fn set_default_mint_limit(
    parameters: &mut Value,
    default_mint_limit: i64,
) -> Result<(), Error> {
    parameters
        .get_mut("ibc_params")
        .ok_or_else(|| eyre!("expect ibc_params section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "default_mint_limit".to_string(),
            Value::String(default_mint_limit.to_string()),
        );

    Ok(())
}

pub fn set_default_per_epoch_throughput_limit(
    parameters: &mut Value,
    default_per_epoch_throughput_limit: i64,
) -> Result<(), Error> {
    parameters
        .get_mut("ibc_params")
        .ok_or_else(|| eyre!("expect ibc_params section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "default_per_epoch_throughput_limit".to_string(),
            Value::String(default_per_epoch_throughput_limit.to_string()),
        );

    Ok(())
}

pub fn set_epochs_per_year(parameters: &mut Value, epochs_per_year: i64) -> Result<(), Error> {
    parameters
        .get_mut("parameters")
        .ok_or_else(|| eyre!("expect parameters section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "epochs_per_year".to_string(),
            Value::Integer(epochs_per_year),
        );

    Ok(())
}
