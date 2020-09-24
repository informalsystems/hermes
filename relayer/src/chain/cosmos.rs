use prost_types::Any;
use std::str::FromStr;
use std::time::Duration;

use tendermint::abci::Path as TendermintABCIPath;
use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::block::Height;
use tendermint::lite::TrustThresholdFraction;
use tendermint_rpc::Client as RpcClient;

use core::future::Future;
use ibc::ics07_tendermint::client_state::ClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState;
use ibc::ics24_host::{Path, IBC_QUERY_PATH};

use crate::client::rpc_requester::RpcRequester;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

use super::Chain;

pub struct CosmosSDKChain {
    config: ChainConfig,
    rpc_client: RpcClient,
    requester: RpcRequester,
}

impl CosmosSDKChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, Error> {
        // TODO: Derive Clone on RpcClient in tendermint-rs
        let requester = RpcRequester::new(RpcClient::new(config.rpc_addr.clone()));
        let rpc_client = RpcClient::new(config.rpc_addr.clone());

        Ok(Self {
            config,
            rpc_client,
            requester,
        })
    }
}

impl Chain for CosmosSDKChain {
    type Header = TMHeader;
    type Commit = TMCommit;
    type ConsensusState = ConsensusState;
    type ClientState = ClientState;
    type Requester = RpcRequester;
    type Error = anomaly::Error<Kind>;

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

    /// Send a transaction that includes the specified messages
    fn send(&self, _msgs: &[Any]) -> Result<(), Error> {
        // TODO sign and broadcast_tx
        Ok(())
    }

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &RpcClient {
        &self.rpc_client
    }

    fn requester(&self) -> &Self::Requester {
        &self.requester
    }

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn unbonding_period(&self) -> Duration {
        // TODO - query chain
        Duration::from_secs(24 * 7 * 3)
    }

    fn trust_threshold(&self) -> TrustThresholdFraction {
        TrustThresholdFraction::default()
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
