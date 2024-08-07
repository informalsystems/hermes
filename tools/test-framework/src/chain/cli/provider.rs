use eyre::eyre;
use std::collections::HashMap;
use std::str;

use crate::chain::exec::{simple_exec, ExecOutput};
use crate::error::{handle_generic_error, Error};

pub fn submit_consumer_chain_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    fees: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/consumer_proposal.json", home_path);

    // The submission might fail silently if there is not enough gas
    let raw_output = simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "gov",
            "submit-legacy-proposal",
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
            "--fees",
            fees,
            "--output",
            "json",
            "--yes",
        ],
    )?;

    let output: serde_json::Value =
        serde_json::from_str(&raw_output.stdout).map_err(handle_generic_error)?;

    let output_code = output.get("code").and_then(|code| code.as_u64()).ok_or_else(|| Error::generic(eyre!("failed to extract 'code' from 'tx gov submit-legacy-proposal consumer-addition' command")))?;

    if output_code != 0 {
        let output_logs = output.get("raw_log").and_then(|code| code.as_str()).ok_or_else(|| Error::generic(eyre!("failed to extract 'raw_logs' from 'tx gov submit-legacy-proposal consumer-addition' command")))?;
        return Err(Error::generic(eyre!("output code for commande 'tx gov submit-legacy-proposal consumer-addition' should be 0, but is instead '{output_code}'. Detail: {output_logs}", )));
    }

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
