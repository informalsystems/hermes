use std::{
    collections::HashMap,
    str,
};

use crate::{
    chain::exec::{
        simple_exec,
        ExecOutput,
    },
    error::Error,
};

pub fn submit_consumer_chain_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/consumer_proposal.json", home_path);

    // The submission might fail silently if there is not enough gas
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
            "--gas",
            "2000000",
            "--yes",
        ],
    )?;

    Ok(())
}

pub fn query_gov_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    proposal_id: &str,
) -> Result<ExecOutput, Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "query",
            "gov",
            "proposal",
            proposal_id,
            "--output",
            "json",
        ],
    )
}

pub fn query_consumer_genesis(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    consumer_chain_id: &str,
    consumer_command_path: &str,
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

    // Neutron does not have the `PreCCV` configuration in its genesis file,
    // and will panic due to an unknown configuration if it is set
    let consumer_genesis = if consumer_command_path == "neutrond" {
        let mut queried_genesis: HashMap<String, serde_json::Value> =
            serde_json::from_str(&exec_output.stdout).expect("failed to read file");

        queried_genesis.remove("preCCV");
        serde_json::to_string(&queried_genesis).unwrap()
    } else {
        exec_output.stdout
    };

    Ok(consumer_genesis)
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
