use eyre::eyre;
use std::collections::HashMap;
use std::{str, thread};

use crate::chain::exec::{simple_exec, ExecOutput};
use crate::error::{handle_generic_error, Error};

pub fn submit_consumer_chain_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    fees: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/consumer_proposal_topn.json", home_path);
    thread::sleep(std::time::Duration::from_secs(3));

    // The submission might fail silently if there is not enough gas
    let raw_output = simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "gov",
            "submit-proposal",
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

    // Proposal submission might fail due to account sequence error.
    // Wait a bit and resubmit if the first submission fails
    if output_code != 0 {
        thread::sleep(std::time::Duration::from_secs(3));
        simple_exec(
            chain_id,
            command_path,
            &[
                "tx",
                "gov",
                "submit-proposal",
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
    }

    Ok(())
}

pub fn create_consumer(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    fees: &str,
) -> Result<String, Error> {
    let proposal_file = format!("{}/consumer_proposal.json", home_path);

    // The submission might fail silently if there is not enough gas
    let raw_output = simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "provider",
            "create-consumer",
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

    let hash = output.get("txhash").and_then(|code| code.as_str()).unwrap();

    thread::sleep(std::time::Duration::from_secs(3));

    let hash_output = simple_exec(
        chain_id,
        command_path,
        &[
            "query",
            "tx",
            hash,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "--output",
            "json",
        ],
    )?;

    let hash_output_json: serde_json::Value =
        serde_json::from_str(&hash_output.stdout).map_err(handle_generic_error)?;

    let output_code = output.get("code").and_then(|code| code.as_u64()).ok_or_else(|| Error::generic(eyre!("failed to extract 'code' from 'tx gov submit-legacy-proposal consumer-addition' command")))?;

    if output_code != 0 {
        let output_logs = output.get("raw_log").and_then(|code| code.as_str()).ok_or_else(|| Error::generic(eyre!("failed to extract 'raw_logs' from 'tx gov submit-legacy-proposal consumer-addition' command")))?;
        return Err(Error::generic(eyre!("output code for commande 'tx provider create-consumer' should be 0, but is instead '{output_code}'. Detail: {output_logs}", )));
    }

    let events = hash_output_json
        .get("events")
        .and_then(|code| code.as_array())
        .ok_or_else(|| {
            Error::generic(eyre!(
                "failed to extract 'events' from the output of `create-consumer` CLI"
            ))
        })?;

    let create_consumer_event = events
        .iter()
        .find(|v| v.get("type").and_then(|v| v.as_str()) == Some("create_consumer"))
        .ok_or_else(|| Error::generic(eyre!("failed to extract create_consumer event")))?;

    let attributes = create_consumer_event
        .get("attributes")
        .and_then(|v| v.as_array())
        .ok_or_else(|| {
            Error::generic(eyre!(
                "failed to extract attributes from create_consumer event"
            ))
        })?;

    let consumer_id_attribute = attributes
        .iter()
        .find(|v| v.get("key").and_then(|v| v.as_str()) == Some("consumer_id"))
        .ok_or_else(|| Error::generic(eyre!("failed to extract consumer_id attribute")))?;

    let consumer_id = consumer_id_attribute
        .get("value")
        .and_then(|v| v.as_str())
        .ok_or_else(|| Error::generic(eyre!("failed to extract consumer_id")))?;

    Ok(consumer_id.to_owned())
}

pub fn validator_opt_in(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    fees: &str,
    consumer_id: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "provider",
            "opt-in",
            consumer_id,
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

    Ok(())
}

pub fn update_consumer(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    fees: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/consumer_update_proposal.json", home_path);

    // The submission might fail silently if there is not enough gas
    let raw_output = simple_exec(
        chain_id,
        command_path,
        &[
            "tx",
            "provider",
            "update-consumer",
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
