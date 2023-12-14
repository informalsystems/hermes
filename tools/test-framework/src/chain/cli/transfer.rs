/*!
   Methods for performing IBC token transfer on a chain.
*/

use crate::{
    chain::exec::simple_exec,
    error::Error,
};

pub fn local_transfer_token(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    sender: &str,
    recipient: &str,
    token: &str,
) -> Result<(), Error> {
    simple_exec(
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
            "--yes",
        ],
    )?;

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
