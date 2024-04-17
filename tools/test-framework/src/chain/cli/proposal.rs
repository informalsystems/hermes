/*!
   Methods for voting on a proposal.
*/
use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::prelude::ChainDriver;

pub fn vote_proposal(driver: &ChainDriver, proposal_id: &str, fees: &str) -> Result<(), Error> {
    simple_exec(
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
            "--gas",
            "auto",
            "--yes",
            "--output",
            "json",
        ],
    )?;

    Ok(())
}

pub fn deposit_proposal(
    driver: &ChainDriver,
    proposal_id: &str,
    amount: &str,
) -> Result<(), Error> {
    simple_exec(
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
            "auto",
            "--yes",
            "--output",
            "json",
        ],
    )?;

    Ok(())
}
