use std::time::Duration;

use anomaly::fail;
use prost_types::Any;
use serde::{de::DeserializeOwned, Serialize};

use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics24_host::Path;

use crate::keyring::store::{KeyEntry, KeyRing};

use crate::client::LightClient;
use crate::config::ChainConfig;
use crate::error;
use crate::util::block_on;

use std::error::Error;

pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;

pub mod handle;
use ibc::tx_msg::Msg;

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
    fn query(&self, data: Path, height: Height, prove: bool) -> Result<Vec<u8>, Self::Error>;

    /// send a transaction with `msgs` to chain.
    fn send(
        &mut self,
        msg_type: String,
        msg: Vec<u8>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<Vec<u8>, Self::Error>;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        &self.config().id
    }

    /// Returns the chain's configuration
    fn config(&self) -> &ChainConfig;

    /// Get a low-level RPC client for this chain
    fn rpc_client(&self) -> &Self::RpcClient;

    /// Get a light client for this chain
    fn light_client(&self) -> Option<&Self::LightClient>;

    /// Set a light client for this chain
    fn set_light_client(&mut self, light_client: Self::LightClient);

    /// The unbonding period of this chain
    /// TODO - this is a GRPC query, needs to be implemented
    fn unbonding_period(&self) -> Duration;

    /// The trust threshold configured for this chain
    fn trust_threshold(&self) -> TrustThreshold;

    /// Query a header at the given height via RPC
    fn query_header_at_height(&self, height: Height) -> Result<Self::LightBlock, error::Error>;

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<Height, error::Error> {
        let status =
            block_on(self.rpc_client().status()).map_err(|e| error::Kind::Rpc.context(e))?;

        if status.sync_info.catching_up {
            fail!(
                error::Kind::LightClient,
                "node at {} running chain {} not caught up",
                self.config().rpc_addr,
                self.config().id,
            );
        }

        Ok(status.sync_info.latest_block_height)
    }

    /// Query the latest header via RPC
    fn query_latest_header(&self) -> Result<Self::LightBlock, error::Error> {
        let height = self.query_latest_height()?;
        self.query_header_at_height(height)
    }
}
