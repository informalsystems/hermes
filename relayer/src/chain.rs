pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;

pub mod handle;
pub mod runtime;

use std::error::Error;
use std::time::Duration;

use anomaly::fail;
use prost_types::Any;
use serde::{de::DeserializeOwned, Serialize};

// TODO: Switch to ibc::Height
use tendermint::{block::Height, chain};
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics24_host::Path;
use ibc::tx_msg::Msg;
use ibc::{events::IBCEvent, ics02_client::client_def::AnyHeader};
use ibc::{ics02_client::client_def::AnyClientState, ics24_host::identifier::ChainId};
use ibc::{
    ics02_client::state::{ClientState, ConsensusState},
    ics04_channel::packet::Packet,
};

use crate::client::LightClient;
use crate::config::ChainConfig;
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::util::block_on;

/// TODO: delete everything below here. `Chain` will be superseded by ChainRuntime & ChainHandle.

/// Defines a blockchain as understood by the relayer
pub trait Chain {
    /// Type of headers for this chain
    type Header: Send + Sync + Serialize + DeserializeOwned;

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
        acct_seq: u64,
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
    fn query_header_at_height(&self, height: Height) -> Result<Self::Header, crate::error::Error>;

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, crate::error::Error>;

    fn assemble_client_state(
        &self,
        header: &Self::Header,
    ) -> Result<Self::ClientState, crate::error::Error>;

    fn assemble_consensus_state(
        &self,
        header: &Self::Header,
    ) -> Result<Self::ConsensusState, crate::error::Error>;

    /// Query the latest height the chain is at via a RPC query
    fn query_latest_height(&self) -> Result<Height, crate::error::Error> {
        let status =
            block_on(self.rpc_client().status()).map_err(|e| crate::error::Kind::Rpc.context(e))?;

        if status.sync_info.catching_up {
            fail!(
                crate::error::Kind::LightClient,
                "node at {} running chain {} not caught up",
                self.config().rpc_addr,
                self.config().id,
            );
        }

        Ok(status.sync_info.latest_block_height)
    }

    /// Query the latest header via RPC
    fn query_latest_header(&self) -> Result<Self::Header, crate::error::Error> {
        let height = self.query_latest_height()?;
        self.query_header_at_height(height)
    }
}
