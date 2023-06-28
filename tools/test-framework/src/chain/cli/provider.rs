use std::str;

use crate::chain::exec::simple_exec;
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
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    consumer_chain_id: &str,
) -> Result<String, Error> {
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

    Ok(exec_output.stdout)
}

pub fn replace_genesis_state(chain_id: &str, home_path: &str) -> Result<String, Error> {
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

    Ok(exec_output.stdout)
}

pub fn copy_validator_key_pair(
    chain_id: &str,
    provider_home_path: &str,
    consumer_home_path: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        "cp",
        &[
            &format!("{}/config/priv_validator_key.json", provider_home_path),
            &format!("{}/config/priv_validator_key.json", consumer_home_path),
        ],
    )?;

    Ok(())
}
