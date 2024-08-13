use eyre::eyre;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

pub fn query_wasm_list_code(
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
            "wasm",
            "list-codes",
            "--output",
            "json",
        ],
    )?;

    let json_output: serde_json::Value =
        serde_json::from_str(&exec_output.stdout).map_err(handle_generic_error)?;

    let code_id = json_output
        .get("code_infos")
        .and_then(|code_infos| code_infos.as_array())
        .and_then(|code_infos| code_infos.first())
        .and_then(|code_info| code_info.get("code_id"))
        .and_then(|code_infos| code_infos.as_str())
        .ok_or_else(|| eyre!("Failed to retrieve wasm code ID"))?;

    Ok(code_id.to_string())
}

pub fn query_wasm_list_contracts_by_code(
    chain_id: &str,
    command_path: &str,
    home_path: &str,
    rpc_listen_address: &str,
    code_id: &str,
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
            "wasm",
            "list-contract-by-code",
            code_id,
            "--output",
            "json",
        ],
    )?;

    let json_output: serde_json::Value =
        serde_json::from_str(&exec_output.stdout).map_err(handle_generic_error)?;

    let contrat = json_output
        .get("contracts")
        .and_then(|contracts| contracts.as_array())
        .and_then(|contracts| contracts.first())
        .and_then(|contract| contract.as_str())
        .ok_or_else(|| eyre!("Failed to retrieve wasm contract address"))?;

    Ok(contrat.to_string())
}
