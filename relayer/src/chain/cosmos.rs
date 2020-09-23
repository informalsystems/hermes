use std::time::Duration;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::block::Height;
use tendermint_light_client::types::LightBlock;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client;
use tendermint_rpc::HttpClient;

use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use crate::client::tendermint::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use super::Chain;
use bytes::Bytes;
use prost::Message;
use std::future::Future;
use std::str::FromStr;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: HttpClient,
    // light_client: LightClient,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        let rpc_client =
            HttpClient::new(config.rpc_addr.clone()).map_err(|e| Kind::Rpc.context(e))?;

        Ok(Self {
            config,
            rpc_client,
            // light_client,
        })
    }
}

impl Chain for CosmosSDKChain {
    type LightBlock = LightBlock;
    type LightClient = LightClient;
    type RpcClient = HttpClient;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;
    type Error = Error;

    fn query(&self, data: Path, height: u64, prove: bool) -> Result<Vec<u8>, Self::Error> {
        let path = TendermintABCIPath::from_str(IBC_QUERY_PATH).unwrap();
        if !data.is_provable() & prove {
            return Err(Kind::Store
                .context("requested proof for a path in the privateStore")
                .into());
        }
        let response = block_on(abci_query(&self, path, data.to_string(), height, prove))?;

        // Verify response proof, if requested.
        if prove {
            dbg!("Todo: implement proof verification."); // Todo: Verify proof
        }

        Ok(response)
    }

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &HttpClient {
        &self.rpc_client
    }

    // fn light_client(&self) -> &LightClient {
    //     &self.light_client
    // }

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn trust_threshold(&self) -> TrustThreshold {
        TrustThreshold::default()
    }
}

/// Perform a generic `abci_query`, and return the corresponding deserialized response data.
async fn abci_query(
    chain: &CosmosSDKChain,
    path: TendermintABCIPath,
    data: String,
    height: u64,
    prove: bool,
) -> Result<Vec<u8>, anomaly::Error<Kind>> {
    // Use the Tendermint-rs RPC client to do the query.
    let response = chain
        .rpc_client()
        .abci_query(
            Some(path),
            data.into_bytes(),
            match height {
                0 => None,
                _ => Some(Height::from(height)),
            },
            prove,
        )
        .await
        .map_err(|e| Kind::Rpc.context(e))?;

    if !response.code.is_ok() {
        // Fail with response log.
        return Err(Kind::Rpc.context(response.log.to_string()).into());
    }
    if response.value.is_empty() {
        // Fail due to empty response value (nothing to decode).
        return Err(Kind::EmptyResponseValue.into());
    }

    Ok(response.value)
}

/// block on future
pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
