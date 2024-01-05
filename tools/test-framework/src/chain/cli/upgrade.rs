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
    fees: &str,
    proposal_id: &str,
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
            proposal_id,
            "yes",
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--from",
            "validator",
            "--fees",
            fees,
            "--yes",
        ],
    )?;

    Ok(())
}

pub fn submit_gov_proposal(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    signer: &str,
    proposal_file: &str,
) -> Result<(), Error> {
    let proposal_file = format!("{}/{}", home_path, proposal_file);
    simple_exec(
        chain_id,
        command_path,
        &[
            "--node",
            rpc_listen_address,
            "tx",
            "gov",
            "submit-proposal",
            &proposal_file,
            "--chain-id",
            chain_id,
            "--home",
            home_path,
            "--keyring-backend",
            "test",
            "--gas",
            "20000000",
            "--from",
            signer,
            "--output",
            "json",
            "--yes",
        ],
    )?;

    Ok(())
}
