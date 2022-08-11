use crate::error::RegistryError;
use crate::formatter::{UriFormatter, WebSocketFormatter};
use async_trait::async_trait;
use futures::{stream::FuturesUnordered, StreamExt};
use http::Uri;
use ibc_proto::cosmos::bank::v1beta1::query_client::QueryClient;
use tendermint_rpc::{Url, Client, SubscriptionClient, WebSocketClient};
use tokio::time::timeout;
use tokio::time::Duration;

pub trait QueryInputOutput {
    type QueryInput: Send;
    type QueryOutput;
}

#[async_trait]
pub trait QueryContext: QueryInputOutput {
    fn query_error(chain_name: String) -> RegistryError;
    async fn query(query: Self::QueryInput) -> Result<Self::QueryOutput, RegistryError>;

    /// Select a healthy RPC/gRPC address from a list of urls.
    async fn select_healthy(
        chain_name: String,
        urls: Vec<Self::QueryInput>,
    ) -> Result<Self::QueryOutput, RegistryError> {
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

/// Data retrievable from RPC endpoints.
#[derive(Clone, Debug)]
pub struct RpcMandatoryData {
    pub rpc_address: String,
    pub max_block_size: u64,
    pub websocket: Url,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

pub struct RPCQuerier;

impl QueryInputOutput for RPCQuerier {
    type QueryInput = String;
    type QueryOutput = RpcMandatoryData;
}

#[async_trait]
impl QueryContext for RPCQuerier {
    fn query_error(chain_name: String) -> RegistryError {
        RegistryError::no_healthy_rpc(chain_name)
    }

    async fn query(rpc: Self::QueryInput) -> Result<Self::QueryOutput, RegistryError> {
        let websocket_addr = WebSocketFormatter::parse_or_build_address(rpc.as_str())?;

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
            rpc_address: rpc.to_string(),
            max_block_size: latest_consensus_params,
            websocket: websocket_addr,
        })
    }
}

// ----------------- GRPC ------------------

pub struct GRPCQuerier;

impl QueryInputOutput for GRPCQuerier {
    type QueryInput = Uri;
    type QueryOutput = Url;
}

#[async_trait]
impl QueryContext for GRPCQuerier {
    fn query_error(chain_name: String) -> RegistryError {
        RegistryError::no_healthy_grpc(chain_name)
    }

    async fn query(uri: Self::QueryInput) -> Result<Self::QueryOutput, RegistryError> {
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
