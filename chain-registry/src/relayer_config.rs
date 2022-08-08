//! Contains methods to generate a relayer config for a given chain
use crate::{asset_list::AssetList, chain::ChainData, error::RegistryError, utils::Fetch};

use futures::{stream::FuturesUnordered, Future, StreamExt};

use http::Uri;

use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::bank::v1beta1::query_client::QueryClient;
use ibc_relayer::config::types::{MaxMsgNum, MaxTxSize, Memo};
use ibc_relayer::config::{default, filter::PacketFilter, AddressType, ChainConfig, GasPrice};
use ibc_relayer::keyring::Store;
use std::str::FromStr;

use std::time::Duration;

use tendermint_light_client_verifier::types::TrustThreshold;
use tendermint_rpc::{Client, SubscriptionClient, WebSocketClient};
use tokio;
use tokio::time::timeout;

// ----------------- RPC ------------------

/// Data retrievable from RPC endpoints
#[derive(Clone, Debug)]
pub struct RpcMandatoryData {
    pub rpc_address: String,
    pub max_block_size: u64,
    pub websocket: tendermint_rpc::Url,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

/// Retrieves the mandatory data from the RPC endpoint
async fn query_rpc(rpc: &str) -> Result<RpcMandatoryData, RegistryError> {
    let websocket_addr = websocket_from_rpc(rpc)?;

    let (client, driver) = timeout(
        Duration::from_secs(5),
        WebSocketClient::new(websocket_addr.clone()),
    )
    .await
    .map_err(|e| RegistryError::websocket_time_out_error(websocket_addr.to_string(), e))?
    .map_err(|e| RegistryError::websocket_connect_error(websocket_addr.to_string(), e))?;

    let driver_handle = tokio::spawn(async move { driver.run().await });

    let latest_consensus_params = match client.latest_consensus_params().await {
        Ok(response) => response.consensus_params.block.max_bytes,
        Err(e) => {
            return Err(RegistryError::rpc_consensus_params_error(
                rpc.to_string(),
                e,
            ))
        }
    };

    client.close().unwrap();
    let _ = driver_handle.await.unwrap();

    Ok(RpcMandatoryData {
        rpc_address: rpc.to_string(),
        max_block_size: latest_consensus_params,
        websocket: websocket_addr,
    })
}

// ----------------- websocket ------------------

/// Generates a websocket address from a rpc address.
fn websocket_from_rpc(rpc_endpoint: &str) -> Result<tendermint_rpc::Url, RegistryError> {
    let uri = rpc_endpoint
        .parse::<Uri>()
        .map_err(|e| RegistryError::uri_parse_error(rpc_endpoint.to_string(), e))?;

    let builder = Uri::builder();
    match builder
        .scheme("ws")
        .authority(uri.authority().unwrap().clone())
        .path_and_query("/websocket")
        .build()
    {
        Ok(uri) => Ok(tendermint_rpc::Url::from_str(uri.to_string().as_str()).unwrap()),
        Err(e) => Err(RegistryError::unable_to_build_websocket_endpoint(
            rpc_endpoint.to_string(),
            e,
        )),
    }
}

// ----------------- GRPC ------------------

/// Returns a tendermint url if the client can connect to the gRPC server
async fn health_check_grpc(grpc_address: &str) -> Result<tendermint_rpc::Url, RegistryError> {
    let uri = parse_or_build_grpc_endpoint(grpc_address)?;
    let tendermint_url = uri.to_string().parse().unwrap();
    QueryClient::connect(uri)
        .await
        .map_err(|_| RegistryError::unable_to_connect_with_grpc())?;
    Ok(tendermint_url)
}

/// Select a healthy rpc/grpc address from a list of urls
async fn select_healthy<'a, RES, FUNC, FUTURE>(
    urls: &'a [String],
    func: FUNC,
    error: RegistryError,
) -> Result<RES, RegistryError>
where
    RES: Send,
    FUNC: Fn(&'a str) -> FUTURE + Send + Sync + 'static,
    FUTURE: Future<Output = Result<RES, RegistryError>> + Send,
{
    let mut futures: FuturesUnordered<_> = urls.iter().map(|url| func(url)).collect();

    while let Some(result) = futures.next().await {
        if result.is_ok() {
            return result;
        }
    }
    Err(error)
}

/// Parses or builds a valid uri from a grpc address
fn parse_or_build_grpc_endpoint(input: &str) -> Result<Uri, RegistryError> {
    let uri = input
        .parse::<Uri>()
        .map_err(|e| RegistryError::uri_parse_error(input.to_string(), e))?;

    if uri.port().is_none() {
        return Err(RegistryError::grpc_without_port(input.to_string()));
    }

    if uri.scheme().is_none() {
        let builder = Uri::builder();
        return builder
            .scheme("https")
            .authority(input)
            .path_and_query("/")
            .build()
            .map_err(|e| RegistryError::grpc_endpoint_parse_error(input.to_string(), e));
    }

    Ok(uri)
}

/// Generates a ChainConfig for a given chain by fetching data from
/// https://github.com/cosmos/chain-registry.
/// Gas settings are set to default values.
pub async fn hermes_config(chain_name: &str, key_name: &str) -> Result<ChainConfig, RegistryError> {
    let name_string = chain_name.to_string();
    let chain_data_handle = tokio::spawn(async move { ChainData::fetch(name_string).await });
    let name_string = chain_name.to_string();
    let assets_handle = tokio::spawn(async move { AssetList::fetch(name_string).await });

    let chain_data = chain_data_handle.await.unwrap()?;

    let grpc_endpoints: Vec<String> = chain_data
        .apis
        .grpc
        .iter()
        .map(|grpc| grpc.address.to_owned())
        .collect();
    let rpc_endpoints: Vec<String> = chain_data
        .apis
        .rpc
        .iter()
        .map(|rpc| rpc.address.to_owned())
        .collect();

    let clone_name = chain_name.to_string();
    let rpc_handle = tokio::spawn(async move {
        select_healthy(
            &rpc_endpoints,
            query_rpc,
            RegistryError::no_healthy_rpc(clone_name),
        )
        .await
    });

    let clone_name = chain_name.to_string();
    let grpc_handle = tokio::spawn(async move {
        select_healthy(
            &grpc_endpoints,
            health_check_grpc,
            RegistryError::no_healthy_grpc(clone_name),
        )
        .await
    });

    let base = if let Some(asset) = assets_handle.await.unwrap()?.assets.first() {
        asset.base.clone()
    } else {
        return Err(RegistryError::no_asset_found(chain_name.to_string()));
    };

    let rpc_mandatory_data = rpc_handle.await.unwrap()?;
    let grpc_address = grpc_handle.await.unwrap()?;

    Ok(ChainConfig {
        id: ChainId::from_string(&chain_data.chain_id),
        r#type: default::chain_type(),
        rpc_addr: tendermint_rpc::Url::from_str(rpc_mandatory_data.rpc_address.as_str()).unwrap(),
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
        packet_filter: PacketFilter::default(),
        address_type: AddressType::default(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::TEST_CHAINS;

    async fn fetch_chain(chain: &str) {
        hermes_config(chain, "testkey").await.unwrap();
    }

    #[test]
    fn test_fetch_chain_config() {
        use tokio::runtime::Runtime;
        let rt = Runtime::new().unwrap();

        let mut handles = Vec::with_capacity(TEST_CHAINS.len());
        for chain in TEST_CHAINS {
            handles.push(fetch_chain(chain));
        }

        for handle in handles {
            rt.block_on(handle);
        }
    }
}
