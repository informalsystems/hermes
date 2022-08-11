/// Contains functions to query RPC and GRPC endpoints for a given chain
use crate::error::RegistryError;
use crate::formatter::{SimpleWebSocketFormatter, UriFormatter};
use async_trait::async_trait;
use futures::{stream::FuturesUnordered, StreamExt};
use http::Uri;
use ibc_proto::cosmos::bank::v1beta1::query_client::QueryClient;
use std::str::FromStr;
use tendermint_rpc::{Client, SubscriptionClient, Url, WebSocketClient};
use tokio::time::timeout;
use tokio::time::Duration;

/// Input, output and error types for a query
pub trait QueryTypes {
    type QueryInput: Send;
    type QueryOutput;
    type QueryError;
}

#[async_trait]
/// QueryContext is a trait that provides the ability to query a chain from a list of endpoints
pub trait QueryContext: QueryTypes {
    /// Returns an error specific to the query
    fn query_error(chain_name: String) -> Self::QueryError;

    /// Queries an endpoint and return the result
    async fn query(query: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError>;

    /// Queries all healthy endpoints from a list of urls and return the output of the first one to answer.
    async fn query_healthy(
        chain_name: String,
        urls: Vec<Self::QueryInput>,
    ) -> Result<Self::QueryOutput, Self::QueryError> {
        let mut futures: FuturesUnordered<_> =
            urls.into_iter().map(|url| Self::query(url)).collect();

        while let Some(result) = futures.next().await {
            if result.is_ok() {
                return result;
            }
        }
        Err(Self::query_error(chain_name))
    }
}

// ----------------- RPC ------------------

/// Data which must be retrieved from RPC endpoints.
#[derive(Clone, Debug)]
pub struct RpcMandatoryData {
    pub rpc_address: Url,
    pub max_block_size: u64,
    pub websocket: Url,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

pub struct SimpleRpcQuerier;

/// Expected Input and Output to query an RPC endpoint
impl QueryTypes for SimpleRpcQuerier {
    type QueryInput = String;
    type QueryOutput = RpcMandatoryData;
    type QueryError = RegistryError;
}

#[async_trait]
impl QueryContext for SimpleRpcQuerier {
    fn query_error(chain_name: String) -> RegistryError {
        RegistryError::no_healthy_rpc(chain_name)
    }

    /// Convert the RPC url to a WebSocket url, query the endpoint, return the mandatory data from the RPC.
    async fn query(rpc: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError> {
        let websocket_addr = SimpleWebSocketFormatter::parse_or_build_address(rpc.as_str())?;

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
                    websocket_addr.to_string(),
                    e,
                ))
            }
        };

        client.close().map_err(|e| {
            RegistryError::websocket_conn_close_error(websocket_addr.to_string(), e)
        })?;

        driver_handle
            .await
            .map_err(|e| RegistryError::join_error("chain_data_join".to_string(), e))?
            .map_err(|e| RegistryError::websocket_driver_error(websocket_addr.to_string(), e))?;

        Ok(RpcMandatoryData {
            rpc_address: Url::from_str(&rpc)
                .map_err(|e| RegistryError::tendermint_url_parse_error(rpc, e))?,
            max_block_size: latest_consensus_params,
            websocket: websocket_addr,
        })
    }
}

// ----------------- GRPC ------------------

pub struct SimpleGrpcQuerier;

/// Expected Input and Output to query a GRPC endpoint
impl QueryTypes for SimpleGrpcQuerier {
    type QueryInput = Uri;
    type QueryOutput = Url;
    type QueryError = RegistryError;
}

#[async_trait]
impl QueryContext for SimpleGrpcQuerier {
    fn query_error(chain_name: String) -> Self::QueryError {
        RegistryError::no_healthy_grpc(chain_name)
    }
    /// Query the endpoint and return the GRPC url
    async fn query(uri: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError> {
        let tendermint_url = uri
            .to_string()
            .parse()
            .map_err(|e| RegistryError::tendermint_url_parse_error(uri.to_string(), e))?;

        QueryClient::connect(uri)
            .await
            .map_err(|_| RegistryError::unable_to_connect_with_grpc())?;

        Ok(tendermint_url)
    }
}
