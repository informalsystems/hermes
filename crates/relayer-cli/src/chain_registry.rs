//! Contains functions to generate a relayer config for a given chain

use futures::future::join_all;
use http::Uri;
use std::collections::HashMap;
use std::fmt::Display;
use std::marker::Send;
use tokio::task::{JoinError, JoinHandle};
use tracing::trace;

use tendermint_light_client_verifier::types::TrustThreshold;
use tendermint_rpc::Url;

use ibc_chain_registry::asset_list::AssetList;
use ibc_chain_registry::chain::ChainData;
use ibc_chain_registry::error::RegistryError;
use ibc_chain_registry::fetchable::Fetchable;
use ibc_chain_registry::formatter::{SimpleGrpcFormatter, UriFormatter};
use ibc_chain_registry::paths::IBCPath;
use ibc_chain_registry::querier::GrpcHealthCheckQuerier;
use ibc_chain_registry::querier::HermesConfigData;
use ibc_chain_registry::querier::QueryContext;
use ibc_chain_registry::querier::SimpleHermesRpcQuerier;
use ibc_relayer::config::filter::{FilterPattern, PacketFilter};
use ibc_relayer::config::gas_multiplier::GasMultiplier;
use ibc_relayer::config::types::{MaxMsgNum, MaxTxSize, Memo};
use ibc_relayer::config::{default, AddressType, ChainConfig, GasPrice};
use ibc_relayer::keyring::Store;

const MAX_HEALTHY_QUERY_RETRIES: u8 = 5;

/// Generate packet filters from Vec<IBCPath> and load them in a Map(chain_name -> filter).
fn construct_packet_filters(ibc_paths: Vec<IBCPath>) -> HashMap<String, PacketFilter> {
    let mut packet_filters: HashMap<_, Vec<_>> = HashMap::new();

    for path in ibc_paths {
        for channel in path.channels {
            let chain_1 = path.chain_1.chain_name.to_owned();
            let chain_2 = path.chain_2.chain_name.to_owned();

            let filters_1 = packet_filters.entry(chain_1).or_default();

            filters_1.push((
                FilterPattern::Exact(channel.chain_1.port_id.clone()),
                FilterPattern::Exact(channel.chain_1.channel_id.clone()),
            ));

            let filters_2 = packet_filters.entry(chain_2).or_default();

            filters_2.push((
                FilterPattern::Exact(channel.chain_2.port_id.clone()),
                FilterPattern::Exact(channel.chain_2.channel_id.clone()),
            ));
        }
    }

    packet_filters
        .into_iter()
        .map(|(k, v)| (k, PacketFilter::allow(v)))
        .collect()
}

/// Generates a ChainConfig for a given chain from ChainData, AssetList, and an optional PacketFilter.
async fn hermes_config<GrpcQuerier, RpcQuerier, GrpcFormatter>(
    chain_data: ChainData,
    assets: AssetList,
    packet_filter: Option<PacketFilter>,
) -> Result<ChainConfig, RegistryError>
where
    GrpcQuerier:
        QueryContext<QueryInput = Uri, QueryOutput = Url, QueryError = RegistryError> + Send,
    RpcQuerier: QueryContext<
            QueryInput = String,
            QueryOutput = HermesConfigData,
            QueryError = RegistryError,
        > + Send,
    GrpcFormatter: UriFormatter<OutputFormat = Uri>,
{
    let chain_name = chain_data.chain_name;

    let asset = assets
        .assets
        .first()
        .ok_or_else(|| RegistryError::no_asset_found(chain_name.to_string()))?;

    let grpc_endpoints = chain_data
        .apis
        .grpc
        .iter()
        .map(|grpc| GrpcFormatter::parse_or_build_address(grpc.address.as_str()))
        .collect::<Result<_, _>>()?;

    let rpc_endpoints: Vec<String> = chain_data
        .apis
        .rpc
        .iter()
        .map(|rpc| rpc.address.to_owned())
        .collect();

    let rpc_data = query_healthy_retry::<RpcQuerier>(
        chain_name.to_string(),
        rpc_endpoints,
        MAX_HEALTHY_QUERY_RETRIES,
    )
    .await?;
    let grpc_address = query_healthy_retry::<GrpcQuerier>(
        chain_name.to_string(),
        grpc_endpoints,
        MAX_HEALTHY_QUERY_RETRIES,
    )
    .await?;
    let websocket_address =
        rpc_data.websocket.clone().try_into().map_err(|e| {
            RegistryError::websocket_url_parse_error(rpc_data.websocket.to_string(), e)
        })?;

    Ok(ChainConfig {
        id: chain_data.chain_id,
        r#type: default::chain_type(),
        rpc_addr: rpc_data.rpc_address,
        websocket_addr: websocket_address,
        grpc_addr: grpc_address,
        rpc_timeout: default::rpc_timeout(),
        genesis_restart: None,
        account_prefix: chain_data.bech32_prefix,
        key_name: String::new(),
        key_store_type: Store::default(),
        key_store_folder: None,
        store_prefix: "ibc".to_string(),
        default_gas: Some(100000),
        max_gas: Some(400000),
        gas_adjustment: None,
        gas_multiplier: Some(GasMultiplier::new(1.1).unwrap()),
        fee_granter: None,
        max_msg_num: MaxMsgNum::default(),
        max_tx_size: MaxTxSize::default(),
        max_grpc_decoding_size: None,
        clock_drift: default::clock_drift(),
        max_block_time: default::max_block_time(),
        trusting_period: None,
        ccv_consumer_chain: false,
        memo_prefix: Memo::default(),
        proof_specs: Default::default(),
        trust_threshold: TrustThreshold::default(),
        gas_price: GasPrice {
            price: 0.1,
            denom: asset.base.to_owned(),
        },
        packet_filter: packet_filter.unwrap_or_default(),
        address_type: AddressType::default(),
        sequential_batch_tx: false,
        extension_options: Vec::new(),
    })
}

/// Concurrent `query_healthy` might fail, this is a helper function which will retry a failed query a fixed
/// amount of times in order to avoid failure with healthy endpoints.
async fn query_healthy_retry<QuerierType>(
    chain_name: String,
    endpoints: Vec<QuerierType::QueryInput>,
    retries: u8,
) -> Result<QuerierType::QueryOutput, RegistryError>
where
    QuerierType: QueryContext + Send,
    QuerierType::QueryInput: Clone + Display,
    QuerierType: QueryContext<QueryError = RegistryError>,
{
    for i in 0..retries {
        let query_response =
            QuerierType::query_healthy(chain_name.to_string(), endpoints.clone()).await;
        match query_response {
            Ok(r) => {
                return Ok(r);
            }
            Err(_) => {
                trace!("Retry {i} failed to query all endpoints");
            }
        }
    }
    Err(RegistryError::unhealthy_endpoints(
        endpoints
            .iter()
            .map(|endpoint| endpoint.to_string())
            .collect(),
        retries,
    ))
}

async fn get_handles<T: Fetchable + Send + 'static>(
    resources: &[String],
    commit: &Option<String>,
) -> Vec<JoinHandle<Result<T, RegistryError>>> {
    let handles = resources
        .iter()
        .map(|resource| {
            let resource = resource.to_string();
            let commit = commit.clone();
            tokio::spawn(async move { T::fetch(resource, commit).await })
        })
        .collect();
    handles
}

async fn get_data_from_handles<T>(
    handles: Vec<JoinHandle<Result<T, RegistryError>>>,
    error_task: &str,
) -> Result<Vec<T>, RegistryError> {
    let data_array: Result<Vec<_>, JoinError> = join_all(handles).await.into_iter().collect();
    let data_array: Result<Vec<T>, RegistryError> = data_array
        .map_err(|e| RegistryError::join_error(error_task.to_string(), e))?
        .into_iter()
        .collect();
    data_array
}

/// Generates a `Vec<ChainConfig>` for a slice of chains names by fetching data from
/// <https://github.com/cosmos/chain-registry>. Gas settings are set to default values.
///
/// # Arguments
///
/// * `chains` - A slice of strings that holds the name of the chains for which a `ChainConfig` will be generated. It must be sorted.
/// * `commit` - An optional String representing the commit hash from which the chain configs will be generated. If it's None, the latest commit will be used.
///
/// # Example
///
/// ```
/// use ibc_relayer_cli::chain_registry::get_configs;
/// let chains = &vec!["cosmoshub".to_string(), "osmosis".to_string()];
/// let configs = get_configs(chains, None);
/// ```
pub async fn get_configs(
    chains: &[String],
    commit: Option<String>,
) -> Result<Vec<ChainConfig>, RegistryError> {
    let n = chains.len();
    if n == 0 {
        return Ok(Vec::new());
    }

    // Spawn tasks to fetch data from the chain-registry
    let chain_data_handle = get_handles::<ChainData>(chains, &commit).await;
    let asset_lists_handle = get_handles::<AssetList>(chains, &commit).await;

    let mut path_handles = Vec::with_capacity(n * (n - 1) / 2);
    for i in 0..n {
        for chain_j in &chains[i + 1..] {
            let chain_i = &chains[i];
            let resource = format!("{chain_i}-{chain_j}.json").to_string();
            let commit_clone = commit.clone();
            path_handles.push(tokio::spawn(async move {
                IBCPath::fetch(resource, commit_clone).await
            }));
        }
    }
    // Collect data from the spawned tasks

    let chain_data_array =
        get_data_from_handles::<ChainData>(chain_data_handle, "chain_data_join").await?;
    let asset_lists =
        get_data_from_handles::<AssetList>(asset_lists_handle, "asset_handle_join").await?;

    let path_data: Result<Vec<_>, JoinError> = join_all(path_handles).await.into_iter().collect();
    let path_data: Vec<IBCPath> = path_data
        .map_err(|e| RegistryError::join_error("path_handle_join".to_string(), e))?
        .into_iter()
        .filter_map(|path| path.ok())
        .collect();

    let mut packet_filters = construct_packet_filters(path_data);

    // Construct ChainConfig
    let config_handles: Vec<JoinHandle<Result<ChainConfig, RegistryError>>> = chain_data_array
        .into_iter()
        .zip(asset_lists.into_iter())
        .zip(chains.iter())
        .map(|((chain_data, assets), chain_name)| {
            let packet_filter = packet_filters.remove(chain_name);
            tokio::spawn(async move {
                hermes_config::<
                        GrpcHealthCheckQuerier,
                        SimpleHermesRpcQuerier,
                        SimpleGrpcFormatter,
                    >(chain_data, assets, packet_filter)
                    .await
            })
        })
        .collect();
    get_data_from_handles::<ChainConfig>(config_handles, "config_handle_join").await
}

/// Concurrent RPC and GRPC queries are likely to fail.
/// Since the RPC and GRPC endpoints are queried to confirm they are healthy,
/// before generating the ChainConfig, the tests must not all run concurrently or
/// else they will fail due to the amount of concurrent queries.
#[cfg(test)]
mod tests {
    use super::*;
    use ibc_relayer::config::filter::ChannelPolicy;
    use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
    use serial_test::serial;
    use std::str::FromStr;

    // Use commit from 28.04.23 for tests
    const TEST_COMMIT: &str = "95b99457e828402bde994816ce57e548d7e1a76d";

    // Helper function for configs without filter. The configuration doesn't have a packet filter
    // if there is no `{chain-a}-{chain-b}.json` file in the `_IBC/` directory of the
    // chain-registry repository: https://github.com/cosmos/chain-registry/tree/master/_IBC
    async fn should_have_no_filter(test_chains: &[String]) -> Result<(), RegistryError> {
        let configs = get_configs(test_chains, Some(TEST_COMMIT.to_owned())).await?;
        for config in configs {
            match config.packet_filter.channel_policy {
                ChannelPolicy::AllowAll => {}
                _ => panic!("PacketFilter not allowed"),
            }
        }

        Ok(())
    }

    #[tokio::test]
    #[serial]
    async fn fetch_chain_config_with_packet_filters() -> Result<(), RegistryError> {
        let test_chains: &[String] = &[
            "cosmoshub".to_string(),
            "juno".to_string(),
            "osmosis".to_string(),
        ]; // Must be sorted

        let configs = get_configs(test_chains, Some(TEST_COMMIT.to_owned())).await?;

        for config in configs {
            match config.packet_filter.channel_policy {
                ChannelPolicy::Allow(channel_filter) => {
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
    #[serial]
    async fn fetch_chain_config_without_packet_filters() -> Result<(), RegistryError> {
        // The commit from 28.04.23 does not have `evmos-juno.json` nor `juno-evmos.json` file:
        // https://github.com/cosmos/chain-registry/tree/master/_IBC
        let test_chains: &[String] = &["evmos".to_string(), "juno".to_string()]; // Must be sorted
        should_have_no_filter(test_chains).await
    }

    #[tokio::test]
    #[serial]
    async fn fetch_one_chain() -> Result<(), RegistryError> {
        let test_chains: &[String] = &["cosmoshub".to_string()]; // Must be sorted
        should_have_no_filter(test_chains).await
    }

    #[tokio::test]
    #[serial]
    async fn fetch_no_chain() -> Result<(), RegistryError> {
        let test_chains: &[String] = &[];
        let configs = get_configs(test_chains, Some(TEST_COMMIT.to_owned())).await?;

        assert_eq!(configs.len(), 0);

        Ok(())
    }
}
