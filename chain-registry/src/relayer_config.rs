//! Contains functions to generate a relayer config for a given chain
use crate::{
    asset_list::AssetList,
    chain::ChainData,
    error::RegistryError,
    formatter::{SimpleGrpcFormatter, UriFormatter},
    paths::IBCPath,
    querier::*,
    utils::Fetchable,
};

use http::Uri;

use ibc_relayer::{
    config::{
        filter::{ChannelFilters, FilterPattern, PacketFilter},
        types::{MaxMsgNum, MaxTxSize, Memo},
        {default, AddressType, ChainConfig, GasPrice},
    },
    keyring::Store,
};

use std::{collections::HashMap, marker::Send};

use tendermint_light_client_verifier::types::TrustThreshold;
use tendermint_rpc::Url;
use tokio;

/// Generate packet filters from Vec<IBCPath> and load them in a Map(chain_name -> filter).
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
async fn hermes_config<GrpcQuerier, RpcQuerier, GrpcFormatter>(
    chain_data: ChainData,
    assets: AssetList,
    packet_filter: Option<PacketFilter>,
    key_name: String,
) -> Result<ChainConfig, RegistryError>
where
    GrpcQuerier:
        QueryContext<QueryInput = Uri, QueryOutput = Url, QueryError = RegistryError> + Send,
    RpcQuerier:
        QueryContext<QueryInput = String, QueryOutput = HermesConfigData, QueryError = RegistryError> + Send,
    GrpcFormatter: UriFormatter<OutputFormat = Uri>,
{
    let chain_name = chain_data.chain_name;

    let mut grpc_endpoints = Vec::new();

    for grpc in chain_data.apis.grpc.iter() {
        grpc_endpoints.push(GrpcFormatter::parse_or_build_address(
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
        tokio::spawn(async move { RpcQuerier::query_healthy(clone_name, rpc_endpoints).await });

    let clone_name = chain_name.to_string();
    let grpc_handle =
        tokio::spawn(async move { GrpcQuerier::query_healthy(clone_name, grpc_endpoints).await });

    let base = if let Some(asset) = assets.assets.first() {
        asset.base.clone()
    } else {
        return Err(RegistryError::no_asset_found(chain_name.to_string()));
    };

    let rpc_data = rpc_handle
        .await
        .map_err(|e| RegistryError::join_error("rpc_data_join".to_string(), e))??;
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
        rpc_addr: rpc_data.rpc_address,
        websocket_addr: rpc_data.websocket,
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

/// Generates a Vec<ChainConfig> for a slice of chains names by fetching data from
/// https://github.com/cosmos/chain-registry. Gas settings are set to default values.
///
/// # Arguments
///
/// * `chains` - A slice of strings that holds the name of the chains for which a `ChainConfig` will be generated. It must be sorted.
/// * `keys` - A slice of keys that holds the name of the keys which will be used for each chain. It must have the same length as `chains`.
/// 
/// # Example
///
/// ```
/// use chain_registry::relayer_config::get_configs;
/// let chains = &vec!["cosmoshub".to_string(), "osmosis".to_string()];
/// let keys = &vec!["key_cosmoshub".to_string(), "key_osmosis".to_string()];
/// let configs = get_configs(chains, keys);
/// ```
pub async fn get_configs(
    chains: &[String],
    keys: &[String],
) -> Result<Vec<ChainConfig>, RegistryError> {
    let n = chains.len();

    if n == 0 {
        return Ok(Vec::new());
    }

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
            hermes_config::<GrpcHealthCheckQuerier, SimpleHermesRpcQuerier, SimpleGrpcFormatter>(
                chain_data,
                assets,
                packet_filter,
                key,
            )
            .await
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
    use ibc::core::ics24_host::identifier::{ChannelId, PortId};
    use std::str::FromStr;

    async fn fetch_configs(test_chains: &[String]) -> Result<Vec<ChainConfig>, RegistryError> {
        let test_keys: &[String] = &vec!["testkey".to_string(); test_chains.len()];
        Ok(get_configs(test_chains, test_keys).await?)
    }

    // Helper function for configs without filter
    async fn should_have_no_filter(test_chains: &[String]) -> Result<(), RegistryError> {
        let configs = fetch_configs(test_chains).await?;
        for config in configs {
            match config.packet_filter {
                PacketFilter::AllowAll => {}
                _ => panic!("PacketFilter not allowed"),
            }
        }
        Ok(())
    }

    #[tokio::test]
    async fn fetch_chain_config_with_packet_filters() -> Result<(), RegistryError> {
        let test_chains: &[String] = &[
            "cosmoshub".to_string(),
            "juno".to_string(),
            "osmosis".to_string(),
        ]; // Must be sorted

        let configs = fetch_configs(test_chains).await?;

        for config in configs {
            match config.packet_filter {
                PacketFilter::Allow(channel_filter) => {
                    if config.id.as_str().contains("cosmoshub") {
                        assert!(channel_filter.is_exact());
                        let cosmoshub_juno = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-207").unwrap(),
                        );
                        let cosmoshub_osmosis = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-141").unwrap(),
                        );
                        assert!(channel_filter.matches(cosmoshub_juno));
                        assert!(channel_filter.matches(cosmoshub_osmosis));
                        assert!(channel_filter.len() == 2);
                    } else if config.id.as_str().contains("juno") {
                        assert!(channel_filter.is_exact());
                        let juno_cosmoshub = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-1").unwrap(),
                        );
                        let juno_osmosis_1 = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-0").unwrap(),
                        );
                        let juno_osmosis_2 = (
                            &PortId::from_str("wasm.juno1v4887y83d6g28puzvt8cl0f3cdhd3y6y9mpysnsp3k8krdm7l6jqgm0rkn").unwrap(), 
                            &ChannelId::from_str("channel-47").unwrap()
                        );
                        assert!(channel_filter.matches(juno_cosmoshub));
                        assert!(channel_filter.matches(juno_osmosis_1));
                        assert!(channel_filter.matches(juno_osmosis_2));
                        assert!(channel_filter.len() == 3);
                    } else if config.id.as_str().contains("osmosis") {
                        assert!(channel_filter.is_exact());
                        let osmosis_cosmoshub = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-0").unwrap(),
                        );
                        let osmosis_juno_1 = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-42").unwrap(),
                        );
                        let osmosis_juno_2 = (
                            &PortId::from_str("transfer").unwrap(),
                            &ChannelId::from_str("channel-169").unwrap(),
                        );
                        assert!(channel_filter.matches(osmosis_cosmoshub));
                        assert!(channel_filter.matches(osmosis_juno_1));
                        assert!(channel_filter.matches(osmosis_juno_2));
                        assert!(channel_filter.len() == 3);
                    } else {
                        panic!("Unknown chain");
                    }
                }
                _ => panic!("PacketFilter not allowed"),
            }
        }

        Ok(())
    }

    #[tokio::test]
    async fn fetch_chain_config_without_packet_filters() -> Result<(), RegistryError> {
        let test_chains: &[String] = &["cosmoshub".to_string(), "evmos".to_string()]; // Must be sorted
        should_have_no_filter(test_chains).await
    }

    #[tokio::test]
    async fn fetch_one_chain() -> Result<(), RegistryError> {
        let test_chains: &[String] = &["cosmoshub".to_string()]; // Must be sorted
        should_have_no_filter(test_chains).await
    }

    #[tokio::test]
    async fn fetch_no_chain() -> Result<(), RegistryError> {
        let test_chains: &[String] = &[];
        let configs = fetch_configs(test_chains).await?;
        assert_eq!(configs.len(), 0);
        Ok(())
    }
}
