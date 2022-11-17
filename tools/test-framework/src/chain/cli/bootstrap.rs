use core::time::Duration;
use eyre::eyre;
use std::fs;
use std::process::{Command, Stdio};
use std::str;
use std::thread::sleep;

use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::types::process::ChildProcess;
use crate::util::file::pipe_to_file;

pub fn initialize(chain_id: &str, command_path: &str, home_path: &str) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--chain-id",
            chain_id,
            "init",
            chain_id,
        ],
    )?;

    Ok(())
}
pub fn add_wallet(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    wallet_id: &str,
) -> Result<String, Error> {
    let output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "keys",
            "add",
            wallet_id,
            "--keyring-backend",
            "test",
            "--output",
            "json",
        ],
    )?;

    // gaia6 somehow displays result in stderr instead of stdout
    if output.stdout.is_empty() {
        Ok(output.stderr)
    } else {
        Ok(output.stdout)
    }
}

pub fn add_genesis_account(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    wallet_address: &str,
    amounts: &[String],
) -> Result<(), Error> {
    let amounts_str = itertools::join(amounts, ",");

    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "add-genesis-account",
            wallet_address,
            &amounts_str,
        ],
    )?;

    Ok(())
}

pub fn add_genesis_validator(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    wallet_id: &str,
    amount: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "gentx",
            wallet_id,
            "--keyring-backend",
            "test",
            "--chain-id",
            chain_id,
            amount,
        ],
    )?;

    Ok(())
}

pub fn collect_gen_txs(chain_id: &str, command_path: &str, home_path: &str) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &["--home", home_path, "collect-gentxs"],
    )?;

    Ok(())
}

pub fn start_chain(
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    grpc_listen_address: &str,
    extra_start_args: &[&str],
) -> Result<ChildProcess, Error> {
    let base_args = [
        "--home",
        home_path,
        "start",
        "--pruning",
        "nothing",
        "--grpc.address",
        grpc_listen_address,
        "--rpc.laddr",
        rpc_listen_address,
    ];

    let mut args: Vec<&str> = base_args.to_vec();
    args.extend(extra_start_args.iter());

    let mut child = Command::new(command_path)
        .args(&args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| eyre!("expected stdout to be present in child process"))?;

    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| eyre!("expected stderr to be present in child process"))?;

    let stderr_path = format!("{}/stdout.log", home_path);
    let stdout_path = format!("{}/stderr.log", home_path);

    pipe_to_file(stdout, &stdout_path)?;
    pipe_to_file(stderr, &stderr_path)?;

    // Wait for a while and check if the child process exited immediately.
    // If so, return error since we expect the full node to be running in the background.

    sleep(Duration::from_millis(1000));

    let status = child
        .try_wait()
        .map_err(|e| eyre!("error try waiting for child status: {}", e))?;

    match status {
        None => Ok(ChildProcess::new(child)),
        Some(status) => {
            let stdout_output = fs::read_to_string(stdout_path)?;
            let stderr_output = fs::read_to_string(stderr_path)?;

            Err(eyre!(
                "expected full node process to be running, but it exited immediately with exit status {} and output: {}\n{}",
                status,
                stdout_output,
                stderr_output,
            ).into())
        }
    }
}
