use crate::chain::exec::simple_exec;
use crate::error::Error;

pub fn feegrant_grant(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    granter: &str,
    grantee: &str,
    fees: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--chain-id",
            chain_id,
            "--node",
            rpc_listen_address,
            "--keyring-backend",
            "test",
            "tx",
            "feegrant",
            "grant",
            granter,
            grantee,
            "--fees",
            fees,
            "--yes",
        ],
    )?;

    Ok(())
}
