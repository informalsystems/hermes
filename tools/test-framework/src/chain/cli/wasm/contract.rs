use std::path::Path;

use crate::chain::cli::query::query_tx_hash;
use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::prelude::ChainDriver;

pub fn store_wasm_contract(
    driver: &ChainDriver,
    title: &str,
    summary: &str,
    wasm_file: &str,
    authority: &str,
    from: &str,
    deposit: &str,
    fees: &str,
    gas: &str,
) -> Result<String, Error> {
    let output = simple_exec(
        driver.chain_id.as_str(),
        &driver.command_path,
        &[
            "--chain-id",
            driver.chain_id.as_str(),
            "--node",
            &driver.rpc_listen_address(),
            "--home",
            &driver.home_path,
            "--keyring-backend",
            "test",
            "tx",
            "wasm",
            "submit-proposal",
            "wasm-store",
            wasm_file,
            "--title",
            title,
            "--summary",
            summary,
            "--authority",
            authority,
            "--deposit",
            deposit,
            "--output",
            "json",
            "--from",
            from,
            "--fees",
            fees,
            "--yes",
            "--gas",
            gas,
        ],
    )?;

    std::thread::sleep(core::time::Duration::from_secs(1));

    query_tx_hash(
        driver.chain_id.as_str(),
        &driver.command_path,
        &driver.home_path,
        &driver.rpc_listen_address(),
        &output.stdout,
    )?;

    Ok(output.stdout)
}

pub fn store_wasm_client_code(
    driver: &ChainDriver,
    code_path: &Path,
    title: &str,
    summary: &str,
    signer: &str,
) -> Result<String, Error> {
    let output = simple_exec(
        driver.chain_id.as_str(),
        &driver.command_path,
        &[
            "tx",
            "ibc-wasm",
            "store-code",
            code_path.to_str().unwrap(),
            "--title",
            title,
            "--summary",
            summary,
            "--chain-id",
            driver.chain_id.as_str(),
            "--node",
            &driver.rpc_listen_address(),
            "--home",
            &driver.home_path,
            "--from",
            signer,
            "--keyring-backend",
            "test",
            "--gas",
            "auto",
            "--deposit",
            "200000stake",
            "-y",
            "--output",
            "json",
        ],
    )?;

    Ok(output.stdout)
}

pub fn instantiate_wasm_contract(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    address: &str,
    fees: &str,
    code: &str,
    init_args: &str,
) -> Result<(), Error> {
    let exec_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--chain-id",
            chain_id,
            "--node",
            rpc_listen_address,
            "--keyring-backend",
            "test",
            "tx",
            "wasm",
            "instantiate",
            code,
            init_args,
            "--from",
            address,
            "--yes",
            "--label",
            "echo",
            "--no-admin",
            "--fees",
            fees,
            "--output",
            "json",
        ],
    )?;

    std::thread::sleep(core::time::Duration::from_secs(1));

    query_tx_hash(
        chain_id,
        command_path,
        home_path,
        rpc_listen_address,
        &exec_output.stdout,
    )?;

    Ok(())
}
