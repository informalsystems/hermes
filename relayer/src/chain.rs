use std::time::Duration;

use anomaly::fail;
use serde::{de::DeserializeOwned, Serialize};

use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics24_host::Path;

use crate::client::LightClient;
use crate::config::ChainConfig;
use crate::error;

use std::error::Error;

mod cosmos;
pub use cosmos::CosmosSDKChain;

/// Defines a blockchain as understood by the relayer
pub trait Chain {
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync + Serialize + DeserializeOwned;

    /// Type of light client for this chain
    type LightClient: LightClient<Self::LightBlock> + Send + Sync;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState + Send + Sync + Serialize + DeserializeOwned;

    /// Type of the client state for this chain
    type ClientState: ClientState + Send + Sync + Serialize + DeserializeOwned;

    /// Type of RPC requester (wrapper around low-level RPC client) for this chain
    type RpcClient: RpcClient + Send + Sync;

    /// Error types defined by this chain
    type Error: Into<Box<dyn Error + Send + Sync + 'static>>;

    /// Perform a generic `query`, and return the corresponding response data.
    fn query(&self, data: Path, height: u64, prove: bool) -> Result<Vec<u8>, Self::Error>;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        &self.config().id
    }

    /// Returns the chain's configuration
    fn config(&self) -> &ChainConfig;

    /// Get a low-level RPC client for this chain
    fn rpc_client(&self) -> &Self::RpcClient;

    // /// Get a light client for this chain
    // fn light_client(&self) -> &Self::LightClient;

    /// The trusting period configured for this chain
    fn trusting_period(&self) -> Duration;

    /// The trust threshold configured for this chain
    fn trust_threshold(&self) -> TrustThreshold;
}

/// Query the latest height the chain is at via a RPC query
pub async fn query_latest_height(chain: &impl Chain) -> Result<Height, error::Error> {
    let status = chain
        .rpc_client()
        .status()
        .await
        .map_err(|e| error::Kind::Rpc.context(e))?;

    if status.sync_info.catching_up {
        fail!(
            error::Kind::LightClient,
            "node at {} running chain {} not caught up",
            chain.config().rpc_addr,
            chain.config().id,
        );
    }

    Ok(status.sync_info.latest_block_height)
}

/// Query a header at the given height via the RPC requester
pub async fn query_header_at_height<C>(
    chain: &C,
    height: Height,
) -> Result<C::LightBlock, error::Error>
where
    C: Chain,
{
    todo!()
}
