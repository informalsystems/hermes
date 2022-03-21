use eyre::eyre;
use serde::Serialize;
use serde_json as json;

use ibc::core::ics24_host::identifier::ConnectionId;

use crate::error::{handle_generic_error, Error};
use crate::prelude::WalletAddress;

use super::ChainDriver;

/// Register a new interchain account controlled by the given account
/// over the given connection.
pub fn register_interchain_account(
    driver: &ChainDriver,
    from: &WalletAddress,
    connection_id: &ConnectionId,
) -> Result<(), Error> {
    let args = &[
        "--home",
        &driver.home_path,
        "--node",
        &driver.rpc_listen_address(),
        "--output",
        "json",
        "tx",
        "intertx",
        "register",
        "--from",
        &from.0,
        "--connection-id",
        connection_id.as_str(),
        "--chain-id",
        driver.chain_id.as_str(),
        "--keyring-backend",
        "test",
        "-y",
    ];

    let res = driver.exec(args)?.stdout;
    check_result_code(&res)?;

    Ok(())
}

/// Query the address of the interchain account
/// corresponding to the given controller account.
pub fn query_interchain_account(
    driver: &ChainDriver,
    account: &WalletAddress,
    connection_id: &ConnectionId,
) -> Result<WalletAddress, Error> {
    let args = &[
        "--home",
        &driver.home_path,
        "--node",
        &driver.rpc_listen_address(),
        "--output",
        "json",
        "query",
        "intertx",
        "interchainaccounts",
        connection_id.as_str(),
        &account.0,
    ];

    let res = driver.exec(args)?.stdout;
    let json_res = json::from_str::<json::Value>(&res).map_err(handle_generic_error)?;

    let address = json_res
        .get("interchain_account_address")
        .ok_or_else(|| eyre!("expected `interchain_account_address` field"))?
        .as_str()
        .ok_or_else(|| eyre!("expected string field"))?;

    Ok(WalletAddress(address.to_string()))
}

/// Submit a msg from a controller account over an ICA channel
/// using the given connection.
pub fn interchain_submit<T: Serialize>(
    driver: &ChainDriver,
    from: &WalletAddress,
    connection_id: &ConnectionId,
    msg: &T,
) -> Result<(), Error> {
    let msg_json = serde_json::to_string_pretty(msg).unwrap();
    println!("{}", msg_json);

    let args = &[
        "--home",
        &driver.home_path,
        "--node",
        &driver.rpc_listen_address(),
        "--output",
        "json",
        "tx",
        "intertx",
        "submit",
        &msg_json,
        "--connection-id",
        connection_id.as_str(),
        "--from",
        &from.0,
        "--chain-id",
        driver.chain_id.as_str(),
        "--keyring-backend",
        "test",
        "-y",
    ];

    let res = driver.exec(args)?.stdout;
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
