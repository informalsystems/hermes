use crate::chain::cli::query::query_tx_hash;
use crate::chain::exec::simple_exec;
use crate::error::Error;

pub fn update_oracle(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    account: &str,
    relayer: &str,
) -> Result<(), Error> {
    let raw_output = simple_exec(
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
            "oracle",
            "update",
            account,
            "--deposit",
            "1000000000000nhash",
            "--from",
            relayer,
            "--fees",
            "381000000nhash",
            "--title",
            "Update oracle",
            "--summary",
            "Update oracle",
            "--output",
            "json",
            "--yes",
        ],
    )?;

    std::thread::sleep(core::time::Duration::from_secs(1));

    query_tx_hash(
        chain_id,
        command_path,
        home_path,
        rpc_listen_address,
        &raw_output.stdout,
    )?;

    Ok(())
}

pub fn async_icq(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    channel_id: &str,
    query_json: &str,
    from: &str,
) -> Result<(), Error> {
    let raw_output = simple_exec(
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
            "oracle",
            "send-query",
            channel_id,
            query_json,
            "--from",
            from,
            "--fees",
            "381000000nhash",
            "--output",
            "json",
            "--yes",
        ],
    )?;

    std::thread::sleep(core::time::Duration::from_secs(1));

    query_tx_hash(
        chain_id,
        command_path,
        home_path,
        rpc_listen_address,
        &raw_output.stdout,
    )?;

    Ok(())
}

pub fn query_oracle_address(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
) -> Result<String, Error> {
    let exec_output = simple_exec(
        chain_id,
        command_path,
        &[
            "--home",
            home_path,
            "--chain-id",
            chain_id,
            "--node",
            rpc_listen_address,
            "query",
            "oracle",
            "address",
        ],
    )?;
    let mut address = exec_output.stdout.replace("address: ", "");
    address.pop();

    Ok(address)
}
