use eyre::eyre;
use serde_json as json;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

/// Register a new interchain account controlled by the given account
/// over the given connection.
pub fn register_interchain_account(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    from: &str,
    connection_id: &str,
) -> Result<(), Error> {
    let args = &[
        "--home",
        home_path,
        "--node",
        rpc_listen_address,
        "--output",
        "json",
        "tx",
        "intertx",
        "register",
        "--from",
        from,
        "--connection-id",
        connection_id,
        "--chain-id",
        chain_id,
        "--keyring-backend",
        "test",
        "-y",
    ];

    let res = simple_exec(chain_id, command_path, args)?.stdout;
    check_result_code(&res)?;

    Ok(())
}

/// Query the address of the interchain account
/// corresponding to the given controller account.
pub fn query_interchain_account(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    account: &str,
    connection_id: &str,
) -> Result<String, Error> {
    let args = &[
        "--home",
        home_path,
        "--node",
        rpc_listen_address,
        "--output",
        "json",
        "query",
        "intertx",
        "interchainaccounts",
        connection_id,
        account,
    ];

    let res = simple_exec(chain_id, command_path, args)?.stdout;
    let json_res = json::from_str::<json::Value>(&res).map_err(handle_generic_error)?;

    let address = json_res
        .get("interchain_account_address")
        .ok_or_else(|| eyre!("expected `interchain_account_address` field"))?
        .as_str()
        .ok_or_else(|| eyre!("expected string field"))?;

    Ok(address.to_string())
}

/// Submit a msg from a controller account over an ICA channel
/// using the given connection.
pub fn interchain_submit(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    from: &str,
    connection_id: &str,
    msg: &str,
) -> Result<(), Error> {
    let args = &[
        "--home",
        home_path,
        "--node",
        rpc_listen_address,
        "--output",
        "json",
        "tx",
        "intertx",
        "submit",
        msg,
        "--connection-id",
        connection_id,
        "--from",
        from,
        "--chain-id",
        chain_id,
        "--keyring-backend",
        "test",
        "-y",
    ];

    let res = simple_exec(chain_id, command_path, args)?.stdout;
    check_result_code(&res)?;

    Ok(())
}

/// Check that a command succeeded, by ensuring that the JSON emitted
/// contains a `code` integer field set to 0.
fn check_result_code(res: &str) -> Result<(), Error> {
    let json_res = json::from_str::<json::Value>(res).map_err(handle_generic_error)?;

    let code = json_res
        .get("code")
        .ok_or_else(|| eyre!("expected `code` field"))?
        .as_i64()
        .ok_or_else(|| eyre!("expected integer field"))?;

    if code == 0 {
        Ok(())
    } else {
        let raw_log = json_res
            .get("raw_log")
            .ok_or_else(|| eyre!("expected `raw_log` field"))?
            .as_str()
            .ok_or_else(|| eyre!("expected string field"))?;

        Err(Error::generic(eyre!("{}", raw_log)))
    }
}
