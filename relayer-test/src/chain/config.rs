/*!
    Helper functions for modifying the Gaia chain config in TOML.

    Since we do not need to understand the full structure of the
    CosmosSDK config, we are updating the config as dynamic TOML
    values instead of serializing them into proper types.
*/

use core::time::Duration;
use eyre::{eyre, Report as Error};
use toml::Value;

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

pub fn set_timeout_commit(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config
        .get_mut("consensus")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "timeout_commit".to_string(),
            format!("{}ms", duration.as_millis()).into(),
        );

    Ok(())
}

pub fn set_timeout_propose(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config
        .get_mut("consensus")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert(
            "timeout_propose".to_string(),
            format!("{}ms", duration.as_millis()).into(),
        );

    Ok(())
}

pub fn set_log_level(config: &mut Value, log_level: &str) -> Result<(), Error> {
    config
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("log_level".to_string(), log_level.into());

    Ok(())
}
