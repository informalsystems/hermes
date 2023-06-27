use std::str;

use crate::chain::driver::ChainDriver;
use crate::chain::exec::simple_exec;
use crate::chain::ext::bootstrap::ChainBootstrapMethodsExt;
use crate::error::Error;

pub fn submit_consumer_chain_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/consumer_proposal.json", home_path);

    simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "gov",
            "submit-proposal",
            "consumer-addition",
            &proposal_file,
            "--chain-id",
            chain_id,
            "--from",
            "validator",
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "--keyring-backend",
            "test",
            "--yes",
        ],
    )?;

    Ok(())
}

pub fn query_consumer_genesis(
    chain_driver: &ChainDriver,
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    consumer_chain_id: &str,
) -> Result<(), Error> {
    let exec_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "query",
            "provider",
            "consumer-genesis",
            consumer_chain_id,
            "--output",
            "json",
        ],
    )?;

    chain_driver.write_file("config/consumer_genesis.json", &exec_output.stdout)?;

    Ok(())
}

pub fn jq_exp(chain_driver: &ChainDriver, home_path: &str, chain_id: &str) -> Result<(), Error> {
    let exec_output = simple_exec(
        chain_id,
        "jq",
        &[
            "-s",
            ".[0].app_state.ccvconsumer = .[1] | .[0]",
            &format!("{}/config/genesis.json", home_path),
            &format!("{}/config/consumer_genesis.json", home_path),
        ],
    )?;

    chain_driver.write_file("config/genesis.json", &exec_output.stdout)?;

    Ok(())
}
