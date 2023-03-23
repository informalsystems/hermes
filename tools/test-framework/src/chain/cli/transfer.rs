/*!
   Methods for performing IBC token transfer on a chain.
*/

use crate::chain::exec::simple_exec;
use crate::error::Error;

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
