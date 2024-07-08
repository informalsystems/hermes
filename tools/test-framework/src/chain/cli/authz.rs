use eyre::eyre;
use std::collections::HashMap;
use std::thread;

use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::prelude::*;

pub fn authz_grant(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    granter: &str,
    grantee: &str,
    msg_type: &str,
    fees: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "--chain-id",
            chain_id,
            "--keyring-backend",
            "test",
            "tx",
            "authz",
            "grant",
            grantee,
            "generic",
            "--msg-type",
            msg_type,
            "--from",
            granter,
            "--fees",
            fees,
            "--yes",
            "--log_format=json",
        ],
    )?;

    Ok(())
}

pub fn query_authz_grant(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    granter: &str,
    grantee: &str,
    msg_type: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "query",
            "authz",
            "grants",
            granter,
            grantee,
            msg_type,
            "--output",
            "json",
        ],
    )?;

    Ok(())
}

pub fn exec_grant(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    ibc_transfer_tx: &str,
    grantee: &str,
    fees: &str,
) -> Result<(), Error> {
    let grant_exec_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "--keyring-backend",
            "test",
            "--chain-id",
            chain_id,
            "tx",
            "authz",
            "exec",
            ibc_transfer_tx,
            "--from",
            grantee,
            "--fees",
            fees,
            "--yes",
            "--output",
            "json",
        ],
    )?;

    let json_res: HashMap<String, serde_json::Value> =
        serde_json::from_str(&grant_exec_output.stdout).map_err(handle_generic_error)?;

    let txhash = json_res
        .get("txhash")
        .ok_or_else(|| eyre!("expect `txhash` string field to be present in json result"))?
        .as_str()
        .ok_or_else(|| eyre!("expected `txhash` to be an array"))?;

    thread::sleep(Duration::from_secs(2));

    let query_txhash_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "query",
            "tx",
            "--type=hash",
            txhash,
            "--output",
            "json",
        ],
    )?;

    let json_res: HashMap<String, serde_json::Value> =
        serde_json::from_str(&query_txhash_output.stdout).map_err(handle_generic_error)?;

    let raw_log = json_res
        .get("raw_log")
        .ok_or_else(|| eyre!("expect `raw_log` string field to be present in json result"))?
        .as_str()
        .ok_or_else(|| eyre!("expected `raw_log` to be a string"))?;

    let code = json_res
        .get("code")
        .ok_or_else(|| eyre!("expect `code` string field to be present in json result"))?
        .as_u64()
        .ok_or_else(|| eyre!("expected `code` to be a u64"))?;

    if !raw_log.is_empty() && code != 0 {
        return Err(Error::generic(eyre!(
            "expected authz exec to succeed but failed with code: {code} and logs: {raw_log}"
        )));
    }
    Ok(())
}
