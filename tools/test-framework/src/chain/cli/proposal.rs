/*!
   Methods for voting on a proposal.
*/
use eyre::eyre;
use tracing::warn;

use crate::chain::cli::query::query_tx_hash;
use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::prelude::{handle_generic_error, ChainDriver};

pub fn vote_proposal(driver: &ChainDriver, proposal_id: &str, fees: &str) -> Result<(), Error> {
    let output = simple_exec(
        driver.chain_id.as_str(),
        &driver.command_path,
        &[
            "tx",
            "gov",
            "vote",
            proposal_id,
            "yes",
            "--chain-id",
            driver.chain_id.as_str(),
            "--home",
            &driver.home_path,
            "--node",
            &driver.rpc_listen_address(),
            "--keyring-backend",
            "test",
            "--from",
            "validator",
            "--fees",
            fees,
            "--yes",
            "--output",
            "json",
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

    Ok(())
}

pub fn deposit_proposal(
    driver: &ChainDriver,
    amount: &str,
    proposal_id: &str,
    fees: &str,
    gas: &str,
) -> Result<(), Error> {
    let output = simple_exec(
        driver.chain_id.as_str(),
        &driver.command_path,
        &[
            "tx",
            "gov",
            "deposit",
            proposal_id,
            amount,
            "--chain-id",
            driver.chain_id.as_str(),
            "--home",
            &driver.home_path,
            "--node",
            &driver.rpc_listen_address(),
            "--keyring-backend",
            "test",
            "--from",
            "validator",
            "--gas",
            gas,
            "--yes",
            "--output",
            "json",
            "--fees",
            fees,
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

    Ok(())
}

pub fn submit_gov_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    signer: &str,
    proposal_file: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/{}", home_path, proposal_file);
    let output = simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "gov",
            "submit-proposal",
            &proposal_file,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--gas",
            "20000000",
            "--from",
            signer,
            "--output",
            "json",
            "--yes",
        ],
    )?;

    let json_output: serde_json::Value =
        serde_json::from_str(&output.stdout).map_err(handle_generic_error)?;

    if json_output
        .get("code")
        .ok_or_else(|| eyre!("expected `code` field in output"))?
        .as_u64()
        .ok_or_else(|| eyre!("expected `code` to be a u64"))?
        != 0
    {
        let raw_log = json_output
            .get("raw_log")
            .ok_or_else(|| eyre!("expected `code` field in output"))?
            .as_str()
            .ok_or_else(|| eyre!("expected `raw_log` to be a str"))?;
        warn!("failed to submit governance proposal due to `{raw_log}`. Will retry...");
        simple_exec(
            chain_id,
            command_path,
            &[
                "--node",
                rpc_listen_address,
                "tx",
                "gov",
                "submit-proposal",
                &proposal_file,
                "--chain-id",
                chain_id,
                "--home",
                home_path,
                "--keyring-backend",
                "test",
                "--gas",
                "20000000",
                "--from",
                signer,
                "--output",
                "json",
                "--yes",
            ],
        )?;
    }

    Ok(())
}
