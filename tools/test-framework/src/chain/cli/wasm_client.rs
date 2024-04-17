use std::path::Path;

use crate::chain::exec::simple_exec;
use crate::prelude::{ChainDriver, Error};

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
            "--fees",
            "1000016stake",
            "--deposit",
            "200000stake",
            "-y",
            "--output",
            "json",
        ],
    )?;

    Ok(output.stdout)
}
