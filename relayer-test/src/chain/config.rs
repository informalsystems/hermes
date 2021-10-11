use toml::Value;
use eyre::{eyre, Report as Error};
use core::time::Duration;

pub fn set_rpc_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config.get_mut("rpc")
        .ok_or_else(|| eyre!("expect rpc section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into());

    Ok(())
}

pub fn set_p2p_port(config: &mut Value, port: u16) -> Result<(), Error> {
    config.get_mut("p2p")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("laddr".to_string(),
            format!("tcp://0.0.0.0:{}", port).into());

    Ok(())
}

pub fn set_timeout_commit(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config.get_mut("consensus")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("timeout_commit".to_string(),
            format!("{}ms", duration.as_millis()).into());

    Ok(())
}

pub fn set_timeout_propose(config: &mut Value, duration: Duration) -> Result<(), Error> {
    config.get_mut("consensus")
        .ok_or_else(|| eyre!("expect p2p section"))?
        .as_table_mut()
        .ok_or_else(|| eyre!("expect object"))?
        .insert("timeout_propose".to_string(),
            format!("{}ms", duration.as_millis()).into());

    Ok(())
}
