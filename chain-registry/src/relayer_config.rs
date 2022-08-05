/// Contains methods to generate a relayer config for a given chain
use crate::{assetlist::AssetList, chain::ChainData, error::RegistryError};
use futures::{stream::FuturesUnordered, StreamExt};
use http::Uri;

use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::bank::v1beta1::query_client::QueryClient;
use ibc_relayer::config::types::{MaxMsgNum, MaxTxSize, Memo};
use ibc_relayer::config::{default, filter::PacketFilter, AddressType, ChainConfig, GasPrice};
use ibc_relayer::keyring::Store;
use std::str::FromStr;

use tendermint_light_client_verifier::types::TrustThreshold;
use tendermint_rpc::{Client, HttpClient};
use tokio;

// ----------------- RPC ------------------

/// Data retrievable from RPC endpoints
#[derive(Clone, Debug)]
pub struct RpcMandatoryData {
    pub rpc_address: String,
    pub max_block_size: u64,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

/// Retrieves the RPC mandatory data from the RPC
async fn query_rpc(rpc: &str) -> Result<RpcMandatoryData, RegistryError> {
    let client =
        HttpClient::new(rpc).map_err(|e| RegistryError::rpc_connect_error(rpc.to_string(), e))?;

    let status = client
        .status()
        .await
        .map_err(|e| RegistryError::rpc_status_error(rpc.to_string(), e))?;

    if status.sync_info.catching_up {
        return Err(RegistryError::rpc_syncing_error(rpc.to_string()));
    }

    let height = status.sync_info.latest_block_height;

    match client.consensus_params(height).await {
        Ok(response) => Ok(RpcMandatoryData {
            rpc_address: rpc.to_string(),
            max_block_size: response.consensus_params.block.max_bytes,
        }),
        Err(e) => {
            Err(RegistryError::rpc_consensus_params_error(
                rpc.to_string(),
                e,
            ))
        }
    }
}

/// Selects a healthy RPC from a list of RPCs
/// An RPC is healthy if it can provide the RpcMandatoryData
async fn select_healthy_rpc(rpcs: &[String]) -> Result<RpcMandatoryData, RegistryError> {
    let mut futures = FuturesUnordered::new();
    rpcs.iter().for_each(|rpc| {
        futures.push(query_rpc(rpc));
    });

    while let Some(result) = futures.next().await {
        if result.is_ok() {
            return result;
        }
    }

    Err(RegistryError::no_healthy_rpc())
}

// ----------------- websocket ------------------

/// Generates a websocket address from a rpc address.
fn websocket_from_rpc(rpc_endpoint: &str) -> Result<tendermint_rpc::Url, RegistryError> {
    match rpc_endpoint.parse::<Uri>() {
        Ok(uri) => {
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
        Err(e) => {
            Err(RegistryError::uri_parse_error(rpc_endpoint.to_string(), e))
        }
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

/// Select a healthy grpc address from a list of grpc addresses
async fn select_healthy_grpc(grpcs: &[String]) -> Result<tendermint_rpc::Url, RegistryError> {
    let mut futures = FuturesUnordered::new();
    grpcs.iter().for_each(|grpc| {
        futures.push(health_check_grpc(grpc));
    });

    while let Some(result) = futures.next().await {
        if result.is_ok() {
            return result;
        }
    }
    Err(RegistryError::no_healthy_grpc())
}

/// Parses or build a valid uri from a grpc address
fn parse_or_build_grpc_endpoint(input: &str) -> Result<Uri, RegistryError> {
    let uri = input
        .parse::<Uri>()
        .map_err(|e| RegistryError::uri_parse_error(input.to_string(), e))?;

    if uri.port().is_none() {
        let builder = Uri::builder();
        return builder
            .build()
            .map_err(|e| RegistryError::grpc_endpoint_parse_error(input.to_string(), e));
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
pub async fn hermes_config(
    chain_name: &'static str,
    key_name: String,
) -> Result<ChainConfig, RegistryError> {
    let chain_data_handle = tokio::spawn(async { ChainData::fetch(chain_name).await });
    let assets_handle = tokio::spawn(async { AssetList::fetch(chain_name).await });

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

    let rpc_handle = tokio::spawn(async move { select_healthy_rpc(&rpc_endpoints).await });

    let grpc_handle = tokio::spawn(async move { select_healthy_grpc(&grpc_endpoints).await });

    let base = if let Some(asset) = assets_handle.await.unwrap()?.assets.first() {
        asset.base.clone()
    } else {
        return Err(RegistryError::no_asset_found(chain_name.to_string()));
    };

    let rpc_mandatory_data = rpc_handle.await.unwrap()?;
    let grpc_address = grpc_handle.await.unwrap()?;

    Ok(ChainConfig {
        id: ChainId::from_string(&chain_data.chain_name),
        r#type: default::chain_type(),
        rpc_addr: tendermint_rpc::Url::from_str(rpc_mandatory_data.rpc_address.as_str()).unwrap(),
        websocket_addr: websocket_from_rpc(&rpc_mandatory_data.rpc_address)?,
        grpc_addr: grpc_address,
        rpc_timeout: default::rpc_timeout(),
        account_prefix: chain_data.bech32_prefix,
        key_name,
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
    // Consider adding a tests for a list of chains

    async fn fetch_cosmoshub_chain() {
        hermes_config("cosmoshub", "testkey".to_string())
            .await
            .unwrap();
    }

    #[test]
    fn test_fetch_cosmoshub_chain() {
        use tokio::runtime::Runtime;
        let rt = Runtime::new().unwrap();
        rt.block_on(fetch_cosmoshub_chain());
    }
}
