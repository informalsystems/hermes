use ibc_proto::Protobuf;
use ibc_relayer::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::Height;
use namada_ibc::storage::{consensus_height, consensus_state_prefix};
use namada_sdk::queries::RPC;
use namada_sdk::storage::{Key, PrefixValue};
use std::fs::File;
use std::io::Read;
use tendermint_rpc::{HttpClient, Url};
use toml::Value;

use crate::prelude::*;

pub fn get_namada_denom_address(
    chain_id: &str,
    home_path: &str,
    denom: &str,
) -> Result<String, Error> {
    let file_path = format!("{}/{}/wallet.toml", home_path, chain_id);
    tracing::warn!("file path: {file_path}");
    let mut toml_content = String::new();
    let mut file = File::open(file_path).expect("Failed to open file");
    file.read_to_string(&mut toml_content)
        .expect("Failed to read file");

    // Parse the TOML content into a `toml::Value` object
    let toml_value: Value = toml::from_str(&toml_content).expect("Failed to parse TOML");

    // Extract a field from the TOML file
    let denom_address = toml_value
        .get("addresses")
        .ok_or_else(|| eyre!("missing `addresses` field"))?
        .get(denom)
        .ok_or_else(|| eyre!("missing `{denom}` field"))?
        .as_str()
        .unwrap_or(denom)
        .to_owned();

    Ok(denom_address)
}

pub async fn query_consensus_states(
    rpc_address: Url,
    client_id: &ClientId,
) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
    // convert to that of ibc-rs
    let client_id = client_id
        .to_string()
        .parse()
        .expect("Client ID conversion shouldn't fail");
    let prefix = consensus_state_prefix(&client_id);
    let mut states = vec![];
    for PrefixValue { key, value } in query_ibc_prefix(rpc_address, &prefix).await? {
        let height = consensus_height(&key).expect("Key should have the height");
        let state = AnyConsensusStateWithHeight {
            height: Height::new(height.revision_number(), height.revision_height()).unwrap(),
            consensus_state: AnyConsensusState::decode_vec(&value)
                .map_err(|_| Error::query_client())?,
        };
        states.push(state);
    }
    Ok(states)
}

async fn query_ibc_prefix(rpc_address: Url, prefix: &Key) -> Result<Vec<PrefixValue>, Error> {
    let client = HttpClient::new(rpc_address).expect("Failed to make a RPC client");
    let response = RPC
        .shell()
        .storage_prefix(&client, None, None, false, &prefix)
        .await
        .map_err(|e| eyre!("Namada query with prefix failed: {e}"))?;
    Ok(response.data)
}
