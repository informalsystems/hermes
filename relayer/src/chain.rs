use std::convert::{TryFrom, TryInto};
use std::time::Duration;

use anomaly::fail;
use prost_types::Any;
use serde::{de::DeserializeOwned, Serialize};

use tendermint_proto::DomainType;

// TODO - tendermint deps should not be here
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics24_host::Path;
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;

use crate::client::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::tx::connection::ConnectionOpenInitOptions;
use crate::util::block_on;

pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;

pub mod handle;

/// Defines a blockchain as understood by the relayer
pub trait Chain {
    /// TODO - Should these be part of the Chain trait?
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync;

    /// Type of light client for this chain
    type LightClient: LightClient<Self::LightBlock> + Send + Sync;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState + Send + Sync;

    /// Type of the client state for this chain
    type ClientState: ClientState + Send + Sync;

    /// Type of RPC requester (wrapper around low-level RPC client) for this chain
    type RpcClient: RpcClient + Send + Sync;
    /// TODO<end>

    /// Error types defined by this chain
    type Error: Into<Box<dyn std::error::Error + Send + Sync + 'static>>;

    /// Perform a generic `query`, and return the corresponding response data.
    fn query(&self, data: Path, height: Height, prove: bool) -> Result<Vec<u8>, Self::Error>;

    /// send a transaction with `msgs` to chain.
    fn send(
        &mut self,
        proto_msgs: Vec<Any>,
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
    /// TODO - Should this be part of the Chain trait?
    fn rpc_client(&self) -> &Self::RpcClient;

    /// Get a light client for this chain
    /// TODO - Should this be part of the Chain trait?
    fn light_client(&self) -> Option<&Self::LightClient>;

    /// Set a light client for this chain
    /// TODO - Should this be part of the Chain trait?
    fn set_light_client(&mut self, light_client: Self::LightClient);

    /// The unbonding period of this chain
    /// TODO - this is a GRPC query, needs to be implemented
    /// TODO - Should this be part of the Chain trait?
    fn unbonding_period(&self) -> Duration;

    /// Query the latest height the chain is at
    fn query_latest_height(&self) -> Result<ICSHeight, Error>;

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
        proof: bool,
    ) -> Result<AnyClientState, Error>;

    fn build_client_state(&self, height: ICSHeight) -> Result<AnyClientState, Error>;

    fn build_consensus_state(&self, height: ICSHeight) -> Result<AnyConsensusState, Error>;

    fn build_header(
        &self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
    ) -> Result<AnyHeader, Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        Ok(CommitmentPrefix::from(
            self.config().store_prefix.as_bytes().to_vec(),
        ))
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: Height,
        proof: bool,
    ) -> Result<ConnectionEnd, Error> {
        Ok(self
            .query(Path::Connections(connection_id.clone()), height, proof)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| ConnectionEnd::decode_vec(&v).map_err(|e| Kind::Query.context(e)))?)
    }
}
