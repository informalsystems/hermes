/*!
   Methods for voting on a proposal.
*/
use crate::chain::exec::simple_exec;
use crate::error::Error;

pub fn vote_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
) -> Result<(), Error> {
    simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "gov",
            "vote",
            "1",
            "yes",
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--from",
            "validator",
            "--yes",
        ],
    )?;

    Ok(())
}
