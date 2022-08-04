/// Contains methods to generate a relayer config for a given chain

use core::time::Duration;

use crate::{
    error::RegistryError,
    chain::{ChainData, Rpc},
    assetlist::AssetList,
};

use futures::{stream::FuturesUnordered, StreamExt};

use http::Uri;

use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::config::ChainConfig;
use ibc_relayer::config::types::{MaxMsgNum, MaxTxSize, Memo};

use tendermint_light_client_verifier::types::TrustThreshold;
use tendermint_rpc::{HttpClient, ClientBuilder};
use tokio;


// flows :
// 1.1 Retrieve chain.json
    // 1.1.1 Retrieve consensus_params.block.max_bytes from RPC /consensus_params. 
    // 1.1.2 max_block_time from RPC /genesis. -------- Impossible to retrieve ? 

// 2.1. Retrieve assets.json
    // 2.1.1 Retrieve denom

// ----------------- RPC ------------------


pub struct RpcMandatoryData {
    pub rpc_address : String,
    pub max_block_size : u64,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

async fn query_rpc(rpc : &str) -> Result<RpcMandatoryData, RegistryError> {
    match HttpClient::new(rpc).await {
        Ok(client) => {
            match client.consensus_params() {
                Ok(genesis) => {
                    Ok(RpcMandatoryData {
                        rpc_address : rpc.to_string(),
                        max_block_size : genesis.consensus_params.max_bytes,
                    })
                },
                Err(e) => {
                    return Err(RegistryError::unable_to_fetch_genesis(rpc.to_string(), e));
                }
            }
        }
        Err(e) => Err(RegistryError::rpc_connect_error(rpc)),
    }
}

async fn select_healthy_rpc(rpcs : &Vec<String>) -> Result<RpcMandatoryData, RegistryError> {
    let mut futures = FuturesUnordered::new();
    rpcs.iter().for_each(|rpc| {
        futures.push(query_rpc(rpc));
    });

    while !futures.is_empty() {
        if let Ok(rpc_mandatory_data) = futures.next().await{
            return Ok(rpc_mandatory_data);
        }
    }

    Err(RegistryError::no_healthy_rpc())
}


fn websocket_from_rpc(rpc_endpoint: &str) -> Result<String, RegistryError> {    
    match rpc_endpoint.parse::<Uri>(){
        Ok(mut uri) => {
            let builder = Uri::builder();
            match builder
            .scheme("ws")
            // this is kind of weird
            .authority(uri.authority().unwrap().clone())
            .path_and_query("/websocket")
            .build() {
                Ok(uri) => Ok(uri.to_string()),
                Err(e) => Err(RegistryError::unable_to_build_websocket_endpoint(rpc_endpoint.to_string(), e)),
            }
        },
        Err(e) => {
            return Err(RegistryError::url_parse_error(rpc_endpoint, e));
        }
    }
}

// ----------------- GRPC ------------------

async fn health_check_grpc(rpc : &str) -> Result<String, RegistryError> {
    todo!()
}

async fn select_healthy_grpc(grpcs : &Vec<String>) -> Result<String, RegistryError> {
    let mut futures = FuturesUnordered::new();
    rpcs.iter().for_each(|grpc| {
        futures.push(health_check_grpc(grpc));
    });

    while !futures.is_empty() {
        if let Ok(healthy_grpc_address) = futures.next().await{
            return Ok(healthy_grpc_address);
        }
    }

    Err(RegistryError::no_healthy_grpc())
}

fn parse_or_build_grpc_endpoint(input: &str) -> Result<String, RegistryError> {
    match rpc_endpoint.parse::<Uri>(){
        Ok(mut uri) => {
            if uri.port().is_none() {
                return Ok("".to_string());
            }
        
            if uri.scheme().is_none() {
                let builder = Uri::builder();
                match builder
                    .scheme("https")
                    // this is kind of weird
                    .authority(input)
                    .path_and_query("/")
                    .build() {
                    Ok(uri) => {
                        return Ok(uri.to_string());
                    },
                    Err(e) => {
                        return Err(RegistryError::grpc_endpoint_parse_error(input.to_string(), e));
                    }
                }
            }
        
            Ok(uri.to_string())
        },
        Err(e) => {
            return Err(RegistryError::url_parse_error(rpc_endpoint, e));
        }
    }
}




async fn hermes_config(chain_name : &str, key_name : String) -> Result<ChainConfig, RegistryError> {

    let chain_data_handle = tokio::spawn(
        async {
            ChainData::fetch(chain_name).await.unwrap().await
        });
    let assets_handle = tokio::spawn(
        async {
            AssetList::fetch(chain_name).await.unwrap().await
        });
    
    let chain_data = chain_data_handle.await?;
    
    
    let grpc_endpoints = chain_data.apis.grpc.map(|grpc| grpc.address);
    let rpc_endpoints = chain_data.apis.rpc.map(|rpc| rpc.address);

    let rpc_handle = tokio::spawn(
        async {
            select_healthy_rpc(&rpc_endpoints).await
        });
    
    let grpc_handle = tokio::spawn(
        async {
            select_healthy_grpc(&grpc_endpoints).await
    });
    
    let base = if let Some(asset) = assets_handle.await?.first() {
        asset.base
    } else {
        return Err(RegistryError::no_assets_found(chain_name.to_string()));
    };

    let rpc_mandatory_data = rpc_handle.await?;
    let grpc_address = grpc_handle.await?;
    
    ChainConfig(
        id : ChainId::from_string(chain_data.chain_name),
        rpc_addr : rpc_mandatory_data.rpc_address,
        websocket_addr : websocket_from_rpc(&rpc_mandatory_data.rpc_address), // TODO
        grpc_addr : grpc_address,
        account_prefix : chain_data.bech32_prefix,
        key_name : key_name,
        store_prefix : "ibc".to_string(),
        default_gas: None, // TODO : default value ? estimation ?
        max_gas: None, // TODO : default value ? estimation ?
        gas_adjustment: None,
        gas_multiplier: None, // TODO : default value ? estimation ?
        max_msg_num : MaxMsgNum::default();
        max_tx_size : MaxTxSize::default();
        clock_drift : Duration::from_secs(5), // TODO : confirm this default value
        max_block_time : Duration::from_secs(30), // TODO : confirm this default value
        gas_price: GasPrice {
            price : 0.1,
            denom : assets.base
        },
        ..ChainConfig::default()
    )   
}