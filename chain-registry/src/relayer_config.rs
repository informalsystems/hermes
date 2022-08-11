//! Contains methods to generate a relayer config for a given chain
use crate::{
    asset_list::AssetList,
    chain::ChainData,
    error::RegistryError,
    formatter::{GRPCFormatter, UriFormatter},
    paths::IBCPath,
    querier::*,
    utils::Fetchable,
};

use ibc_relayer::{
    config::{
        filter::{ChannelFilters, FilterPattern, PacketFilter},
        types::{MaxMsgNum, MaxTxSize, Memo},
        {default, AddressType, ChainConfig, GasPrice},
    },
    keyring::Store,
};

use std::{collections::HashMap, str::FromStr};

use tendermint_light_client_verifier::types::TrustThreshold;
use tokio;

// ----------------- Packet filters ------------------
/// Generate packet filters from Vec<IBCPath>.
fn construct_packet_filters(ibc_paths: Vec<IBCPath>) -> HashMap<String, PacketFilter> {
    let mut packet_filters = HashMap::new();

    for path in ibc_paths {
        for channel in path.channels {
            let chain_1 = path.chain_1.chain_name.to_owned();
            let chain_2 = path.chain_2.chain_name.to_owned();

            let filters_1 = packet_filters.entry(chain_1).or_insert(Vec::new());
            filters_1.push((
                FilterPattern::Exact(channel.chain_1.port_id.clone()),
                FilterPattern::Exact(channel.chain_1.channel_id.clone()),
            ));
            let filters_2 = packet_filters.entry(chain_2).or_insert(Vec::new());
            filters_2.push((
                FilterPattern::Exact(channel.chain_2.port_id.clone()),
                FilterPattern::Exact(channel.chain_2.channel_id.clone()),
            ));
        }
    }

    packet_filters
        .into_iter()
        .map(|(k, v)| (k, PacketFilter::Allow(ChannelFilters::new(v))))
        .collect()
}

/// Generates a ChainConfig for a given chain from ChainData, AssetList and an optional PacketFilter.
async fn hermes_config(
    chain_data: ChainData,
    assets: AssetList,
    packet_filter: Option<PacketFilter>,
    key_name: String,
) -> Result<ChainConfig, RegistryError> {
    let chain_name = chain_data.chain_name;

    let mut grpc_endpoints = Vec::new();

    for grpc in chain_data.apis.grpc.iter() {
        grpc_endpoints.push(GRPCFormatter::parse_or_build_address(
            grpc.address.as_str(),
        )?)
    }

    let rpc_endpoints: Vec<String> = chain_data
        .apis
        .rpc
        .iter()
        .map(|rpc| rpc.address.to_owned())
        .collect();

    let clone_name = chain_name.to_string();
    let rpc_handle =
        tokio::spawn(async move { RPCQuerier::select_healthy(clone_name, rpc_endpoints).await });

    let clone_name = chain_name.to_string();
    let grpc_handle =
        tokio::spawn(async move { GRPCQuerier::select_healthy(clone_name, grpc_endpoints).await });

    let base = if let Some(asset) = assets.assets.first() {
        asset.base.clone()
    } else {
        return Err(RegistryError::no_asset_found(chain_name.to_string()));
    };

    let rpc_mandatory_data = rpc_handle
        .await
        .map_err(|e| RegistryError::join_error("rpc_mandatory_data_join".to_string(), e))??;
    let grpc_address = grpc_handle
        .await
        .map_err(|e| RegistryError::join_error("grpc_handle_join".to_string(), e))??;

    let packet_filter = match packet_filter {
        Some(pf) => pf,
        None => PacketFilter::default(),
    };

    Ok(ChainConfig {
        id: chain_data.chain_id,
        r#type: default::chain_type(),
        rpc_addr: tendermint_rpc::Url::from_str(rpc_mandatory_data.rpc_address.as_str()).map_err(
            |e| RegistryError::tendermint_url_parse_error(rpc_mandatory_data.rpc_address, e),
        )?,
        websocket_addr: rpc_mandatory_data.websocket,
        grpc_addr: grpc_address,
        rpc_timeout: default::rpc_timeout(),
        account_prefix: chain_data.bech32_prefix,
        key_name: key_name.to_string(),
        key_store_type: Store::default(),
        store_prefix: "ibc".to_string(),
        default_gas: Some(100000),
        max_gas: Some(400000),
        gas_adjustment: None,
        gas_multiplier: Some(1.1),
        fee_granter: None,
        max_msg_num: MaxMsgNum::default(),
        max_tx_size: MaxTxSize::default(),
        clock_drift: default::clock_drift(),
        max_block_time: default::max_block_time(),
        trusting_period: None,
        memo_prefix: Memo::default(),
        proof_specs: Default::default(),
        trust_threshold: TrustThreshold::default(),
        gas_price: GasPrice {
            price: 0.1,
            denom: base,
        },
        packet_filter,
        address_type: AddressType::default(),
    })
}

/// Generates a Vec<ChainConfig> for an array of chains by fetching data from
/// https://github.com/cosmos/chain-registry.
/// Gas settings are set to default values.
pub async fn get_configs(
    chains: &[String],
    keys: &[String],
) -> Result<Vec<ChainConfig>, RegistryError> {
    let n = chains.len();
    let mut chain_data_handle = Vec::with_capacity(n);
    let mut asset_lists_handle = Vec::with_capacity(n);
    let mut path_handles = Vec::with_capacity(n * (n - 1) / 2);

    for i in 0..n {
        let chain = chains[i].to_string();
        chain_data_handle.push(tokio::spawn(async move { ChainData::fetch(chain).await }));

        let chain = chains[i].to_string();
        asset_lists_handle.push(tokio::spawn(async move { AssetList::fetch(chain).await }));

        for chain_j in &chains[i + 1..] {
            let chain_i = &chains[i];
            let chain_j = chain_j;
            let resource = format!("{}-{}.json", chain_i, chain_j).to_string();
            path_handles.push(tokio::spawn(async move { IBCPath::fetch(resource).await }));
        }
    }
    // Extract packet filters from IBC paths
    let mut path_data: Vec<IBCPath> = Vec::new();

    for handle in path_handles {
        if let Ok(path) = handle
            .await
            .map_err(|e| RegistryError::join_error("path_handle_join".to_string(), e))?
        {
            path_data.push(path);
        }
    }
    let mut packet_filters = construct_packet_filters(path_data);

    // Construct ChainConfig
    let mut configs_handle = Vec::with_capacity(n);

    for (i, (chain_handle, asset_handle)) in chain_data_handle
        .into_iter()
        .zip(asset_lists_handle.into_iter())
        .enumerate()
    {
        let chain_data = chain_handle
            .await
            .map_err(|e| RegistryError::join_error("chain_data_join".to_string(), e))??;
        let assets = asset_handle
            .await
            .map_err(|e| RegistryError::join_error("asset_handle_join".to_string(), e))??;

        let packet_filter = packet_filters.remove(&chains[i]);
        let key = keys[i].to_string();

        configs_handle.push(tokio::spawn(async move {
            hermes_config(chain_data, assets, packet_filter, key).await
        }));
    }

    let mut configs = Vec::with_capacity(n);
    for handle in configs_handle {
        let config = handle
            .await
            .map_err(|e| RegistryError::join_error("config_handle_join".to_string(), e))??;

        configs.push(config);
    }

    Ok(configs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn fetch_chain_config_with_packet_filters() -> Result<(), RegistryError> {
        let test_chains: &[String] = &[
            "cosmoshub".to_string(),
            "juno".to_string(),
            "osmosis".to_string(),
        ]; // Must be sorted
        let test_keys: &[String] = &[
            "testkey".to_string(),
            "testkey".to_string(),
            "testkey".to_string(),
        ];
        let configs = get_configs(test_chains, test_keys).await?;

        for config in configs {
            match config.packet_filter {
                PacketFilter::Allow(_) => {}
                _ => panic!("PacketFilter not allowed"),
            }
        }

        Ok(())
    }

    #[tokio::test]
    async fn fetch_chain_config_without_packet_filters() -> Result<(), RegistryError> {
        let test_chains: &[String] = &["cosmoshub".to_string(), "evmos".to_string()]; // Must be sorted
        let test_keys: &[String] = &["testkey".to_string(), "testkey".to_string()];
        let configs = get_configs(test_chains, test_keys).await?;

        for config in configs {
            match config.packet_filter {
                PacketFilter::AllowAll => {}
                _ => panic!("PacketFilter not allowed"),
            }
        }

        Ok(())
    }
}
