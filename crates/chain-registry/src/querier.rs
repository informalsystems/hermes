//! Contains traits to query nodes of a given chain from their APIs.
//! Contains struct to perform a health check on a gRPC/WebSocket endpoint and
//! to retrieve the `max_block_size` from a RPC endpoint.

use std::fmt::Debug;
use std::str::FromStr;

use async_trait::async_trait;
use futures::{stream::FuturesUnordered, StreamExt};
use http::Uri;
use tendermint_rpc::HttpClient;
use tendermint_rpc::HttpClientUrl;
use tracing::{debug, info};

use ibc_proto::cosmos::bank::v1beta1::query_client::QueryClient;
use ibc_relayer::util::create_grpc_client;
use ibc_relayer::HERMES_VERSION;
use tendermint_rpc::{Client, Url};

use crate::error::RegistryError;

/// `QueryTypes` represents the basic types required to query a node
pub trait QueryTypes {
    /// `QueryInput` represents the data needed to query a node. It is typically a URL
    type QueryInput: Debug + Send;
    /// `QueryOutput` represents the data returned by your query
    type QueryOutput;
    /// `QueryOutput` represents the error returned when a query fails
    type QueryError;
}

#[async_trait]
/// `QueryContext` represents the basic expectations for a query
pub trait QueryContext: QueryTypes {
    /// Return an error specific to the query which is returned when `query_healthy` fails
    ///
    /// # Arguments
    ///
    /// * `chain_name` - A string slice that holds the name of a chain
    fn query_error(chain_name: String) -> Self::QueryError;

    /// Query an endpoint and return the result
    ///
    /// # Arguments
    ///
    /// * `url` - A `QueryInput` object that holds the data needed to query a node
    async fn query(url: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError>;

    /// Query every endpoint from a list of urls and return the output of the first one to answer.
    ///
    /// # Arguments
    ///
    /// * `chain_name` - A string that holds the name of a chain
    /// * `urls` - A vector of urls to query
    async fn query_healthy(
        chain_name: String,
        urls: Vec<Self::QueryInput>,
    ) -> Result<Self::QueryOutput, Self::QueryError> {
        info!("Trying to find a healthy RPC endpoint for chain {chain_name}");
        debug!("Trying the following RPC endpoints: {urls:?}");

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

/// `SimpleHermesRpcQuerier` retrieves `HermesConfigData` by querying a list of RPC endpoints
/// through their RPC API and returns the result of the first endpoint to answer.
pub struct SimpleHermesRpcQuerier;

/// Data which must be retrieved from RPC endpoints for Hermes
#[derive(Clone, Debug)]
pub struct HermesConfigData {
    pub rpc_address: Url,
    pub max_block_size: u64,
    // max_block_time should also be retrieved from the RPC
    // however it looks like it is not in the genesis file anymore
}

/// Expected Input, Output and Error to query an RPC endpoint
impl QueryTypes for SimpleHermesRpcQuerier {
    type QueryInput = String;
    type QueryOutput = HermesConfigData;
    type QueryError = RegistryError;
}

#[async_trait]
impl QueryContext for SimpleHermesRpcQuerier {
    /// Return an error `NoHealthyRpc` when `query_healthy` fails
    fn query_error(chain_name: String) -> RegistryError {
        RegistryError::no_healthy_rpc(chain_name)
    }

    /// Query the endpoint, return the data from the RPC.
    async fn query(rpc_url: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError> {
        info!("Querying RPC server at {rpc_url}");

        let url = HttpClientUrl::from_str(&rpc_url)
            .map_err(|e| RegistryError::tendermint_url_parse_error(rpc_url.clone(), e))?;

        let client = HttpClient::builder(url)
            .user_agent(format!("hermes/{}", HERMES_VERSION))
            .build()
            .map_err(|e| RegistryError::rpc_connect_error(rpc_url.clone(), e))?;

        let latest_consensus_params = match client.latest_consensus_params().await {
            Ok(response) => response.consensus_params.block.max_bytes,
            Err(e) => {
                return Err(RegistryError::rpc_consensus_params_error(
                    rpc_url.to_string(),
                    e,
                ))
            }
        };

        Ok(HermesConfigData {
            rpc_address: Url::from_str(&rpc_url)
                .map_err(|e| RegistryError::tendermint_url_parse_error(rpc_url, e))?,
            max_block_size: latest_consensus_params,
        })
    }
}

// ----------------- GRPC ------------------

/// `GrpcHealthCheckQuerier` connects to a list of gRPC endpoints
/// and returns the URL of the first one to answer.
pub struct GrpcHealthCheckQuerier;

/// Expected Input and Output to query a GRPC endpoint
impl QueryTypes for GrpcHealthCheckQuerier {
    type QueryInput = Uri;
    type QueryOutput = Url;
    type QueryError = RegistryError;
}

#[async_trait]
impl QueryContext for GrpcHealthCheckQuerier {
    /// Return an error `NoHealthyGrpc` when `query_healthy` fails
    fn query_error(chain_name: String) -> Self::QueryError {
        RegistryError::no_healthy_grpc(chain_name)
    }

    /// Query the endpoint and return the GRPC url
    async fn query(uri: Self::QueryInput) -> Result<Self::QueryOutput, Self::QueryError> {
        let tendermint_url = uri
            .to_string()
            .parse()
            .map_err(|e| RegistryError::tendermint_url_parse_error(uri.to_string(), e))?;

        info!("Querying gRPC server at {tendermint_url}");

        create_grpc_client(&uri, QueryClient::new)
            .await
            .map_err(|_| RegistryError::unable_to_connect_with_grpc())?;

        Ok(tendermint_url)
    }
}
