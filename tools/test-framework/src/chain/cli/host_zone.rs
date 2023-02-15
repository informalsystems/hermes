use crate::chain::exec::simple_exec;
use crate::error::Error;

pub fn register_host_zone(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    connection_id: &str,
    host_denom: &str,
    bech32_prefix: &str,
    ibc_denom: &str,
    channel_id: &str,
    sender: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--node",
            rpc_listen_address,
            "--keyring-backend",
            "test",
            "tx",
            "stakeibc",
            "register-host-zone",
            connection_id,
            host_denom,
            bech32_prefix,
            ibc_denom,
            channel_id,
            "1",
            "--from",
            sender,
            "--chain-id",
            chain_id,
            "--gas",
            "auto",
            "-b",
            "block",
            "--yes",
        ],
    )?;

    Ok(())
}
