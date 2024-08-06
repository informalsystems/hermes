/*!
   Methods for performing IBC token transfer on a chain.
*/
use eyre::eyre;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

pub fn local_transfer_token(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    sender: &str,
    recipient: &str,
    token: &str,
    fees: &str,
) -> Result<(), Error> {
    let raw_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "bank",
            "send",
            sender,
            recipient,
            token,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--fees",
            fees,
            "--output",
            "json",
            "--yes",
        ],
    )?;

    let output: serde_json::Value =
        serde_json::from_str(&raw_output.stdout).map_err(handle_generic_error)?;

    let output_code = output
        .get("code")
        .and_then(|code| code.as_u64())
        .ok_or_else(|| {
            Error::generic(eyre!("failed to extract 'code' from 'tx gov vote' command"))
        })?;

    if output_code != 0 {
        let output_logs = output
            .get("raw_log")
            .and_then(|code| code.as_str())
            .ok_or_else(|| {
                Error::generic(eyre!(
                    "failed to extract 'raw_logs' from 'tx gov vote' command"
                ))
            })?;
        return Err(Error::generic(eyre!("output code for commande 'tx gov vote' should be 0, but is instead '{output_code}'. Detail: {output_logs}", )));
    }

    Ok(())
}

pub fn transfer_from_chain(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    sender: &str,
    src_port: &str,
    src_channel: &str,
    recipient: &str,
    token: &str,
    fees: &str,
    timeout_height: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "ibc-transfer",
            "transfer",
            src_port,
            src_channel,
            recipient,
            token,
            "--from",
            sender,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--fees",
            fees,
            "--timeout-height",
            timeout_height,
            "--yes",
        ],
    )?;

    Ok(())
}

pub fn generate_transfer_from_chain_tx(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    sender: &str,
    src_port: &str,
    src_channel: &str,
    recipient: &str,
    token: &str,
) -> Result<String, Error> {
    let output = simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "ibc-transfer",
            "transfer",
            src_port,
            src_channel,
            recipient,
            token,
            "--from",
            sender,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--generate-only",
        ],
    )?;

    Ok(output.stdout)
}
