use ibc_proto::Protobuf;
use ibc_relayer::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, PortId};
use ibc_relayer_types::events::IbcEventType;
use ibc_relayer_types::Height;
use itertools::Itertools;
use namada_sdk::events::extend::Height as HeightAttr;
use namada_sdk::ibc::storage::{consensus_height, consensus_state_prefix};
use namada_sdk::queries::RPC;
use namada_sdk::storage::{Key, PrefixValue};
use namada_sdk::tx::Tx;
use std::fs::File;
use std::io::Read;
use tendermint_rpc::{Client, HttpClient, Url};
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
    for PrefixValue { key, value } in query_prefix(rpc_address, &prefix).await? {
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

async fn query_prefix(rpc_address: Url, prefix: &Key) -> Result<Vec<PrefixValue>, Error> {
    let client = HttpClient::new(rpc_address).expect("Failed to make a RPC client");
    let response = RPC
        .shell()
        .storage_prefix(&client, None, None, false, prefix)
        .await
        .map_err(|e| eyre!("Namada query with prefix failed: {e}"))?;
    Ok(response.data)
}

pub async fn query_receive_tx_memo(
    rpc_address: Url,
    src_port_id: &PortId,
    src_channel_id: &ChannelId,
    dst_port_id: &PortId,
    dst_channel_id: &ChannelId,
    sequence: Sequence,
) -> Result<String, Error> {
    let client = HttpClient::new(rpc_address).expect("Failed to make a RPC client");
    let height = query_write_ack_packet_height(
        &client,
        src_port_id,
        src_channel_id,
        dst_port_id,
        dst_channel_id,
        sequence,
    )
    .await?;

    let height = tendermint::block::Height::try_from(height.revision_height())
        .expect("Height should be converted");
    let response = client
        .block(height)
        .await
        .map_err(|e| eyre!("Query a block failed: {e}"))?;
    let memo: Vec<String> = response
        .block
        .data
        .iter()
        .flat_map(|tx_bytes| {
            let tx = Tx::try_from(&tx_bytes[..])
                .map_err(|e| e.to_string())
                .expect("Decoding tx failed");
            let memo: Vec<String> = tx
                .header()
                .batch
                .iter()
                .filter_map(|cmt| {
                    tx.memo(cmt)
                        .map(|memo_bytes| String::from_utf8_lossy(&memo_bytes).to_string())
                })
                .collect();
            memo
        })
        .collect();

    // All memo should be the same for now
    assert!(memo.iter().all_equal());

    let memo = memo.first().ok_or_else(|| eyre!("No memo field"))?;
    Ok(memo.to_string())
}

async fn query_write_ack_packet_height(
    client: &HttpClient,
    src_port_id: &PortId,
    src_channel_id: &ChannelId,
    dst_port_id: &PortId,
    dst_channel_id: &ChannelId,
    sequence: Sequence,
) -> Result<Height, Error> {
    let event = RPC
        .shell()
        .ibc_packet(
            client,
            &IbcEventType::WriteAck
                .as_str()
                .parse()
                .expect("IbcEventType should be parsable"),
            &src_port_id
                .as_str()
                .parse()
                .expect("PortId should be parsable"),
            &src_channel_id
                .as_str()
                .parse()
                .expect("ChannelId should be parsable"),
            &dst_port_id
                .as_str()
                .parse()
                .expect("PortId should be parsable"),
            &dst_channel_id
                .as_str()
                .parse()
                .expect("ChannelId should be parsable"),
            &u64::from(sequence).into(),
        )
        .await
        .map_err(|e| eyre!("Namada packet query failed: {e}"))?
        .ok_or_else(|| eyre!("No write ack event"))?;
    let height = event
        .read_attribute::<HeightAttr>()
        .expect("Height should exist");

    Ok(Height::new(0, height.0).expect("Height conversion shouldn't fail"))
}
