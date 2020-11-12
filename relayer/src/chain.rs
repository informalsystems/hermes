use std::convert::{TryFrom, TryInto};
use std::time::Duration;

use anomaly::fail;
use prost_types::Any;
use serde::{de::DeserializeOwned, Serialize};

use tendermint_proto::DomainType;

// TODO - tendermint deps should not be here
//use tendermint::account::Id as AccountId;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::Height as ICSHeight;

use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::version::get_compatible_versions;
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof};
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics24_host::Path;
use ibc::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::tx_msg::Msg;

use crate::client::LightClient;
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::tx::connection::{ConnectionMsgType, ConnectionOpenInitOptions, ConnectionOpenOptions};
use crate::util::block_on;

pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;
pub mod handle;
pub mod runtime;

/// Generic query response type
/// TODO - will slowly move to GRPC protobuf specs for queries
pub struct QueryResponse {
    pub value: Vec<u8>,
    pub proof: MerkleProof,
    pub height: Height,
}

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
    // TODO - migrate callers to use ics_query() and then remove this
    fn query(&self, data: Path, height: Height, prove: bool) -> Result<QueryResponse, Self::Error>;

    /// Perform a generic ICS `query`, and return the corresponding response data.
    fn ics_query(
        &self,
        data: Path,
        height: ICSHeight,
        prove: bool,
    ) -> Result<QueryResponse, Self::Error>;

    /// send a transaction with `msgs` to chain.
    fn send(
        &mut self,
        proto_msgs: Vec<Any>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<String, Self::Error>;

    /// Returns the chain's identifier
    /// TODO - move to ICS Chain Id
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

    /// Query the latest height the chain is at
    fn query_latest_height(&self) -> Result<ICSHeight, Error>;

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<AnyClientState, Error>;

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn build_client_state(&self, height: ICSHeight) -> Result<AnyClientState, Error>;

    fn build_consensus_state(&self, height: ICSHeight) -> Result<AnyConsensusState, Error>;

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        let res = self
            .ics_query(Path::Connections(connection_id.clone()), height, true)
            .map_err(|e| Kind::Query.context(e))?;
        let connection_end =
            ConnectionEnd::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        Ok((connection_end, res.proof))
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: ICSHeight,
        height: ICSHeight,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        let res = self
            .ics_query(
                ClientConsensusPath {
                    client_id: client_id.clone(),
                    epoch: consensus_height.version_number,
                    height: consensus_height.version_height,
                },
                height,
                true,
            )
            .map_err(|e| Kind::Query.context(e))?;
        let consensus_state =
            AnyConsensusState::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        Ok((consensus_state, res.proof))
    }

    fn build_header(
        &self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
    ) -> Result<AnyHeader, Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        // TODO - do a real chain query
        Ok(CommitmentPrefix::from(
            self.config().store_prefix.as_bytes().to_vec(),
        ))
    }

    fn query_compatible_versions(&self) -> Result<Vec<String>, Error> {
        // TODO - do a real chain query
        Ok(get_compatible_versions())
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<ConnectionEnd, Error> {
        Ok(self
            .ics_query(Path::Connections(connection_id.clone()), height, false)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| {
                ConnectionEnd::decode_vec(&v.value).map_err(|e| Kind::Query.context(e))
            })?)
    }

    /// Builds the required proofs and the client state for connection handshake messages.
    /// The proofs and client state must be obtained from queries at same height with value
    /// `height - 1`
    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        // Set the height of the queries at height - 1
        let query_height = height
            .decrement()
            .map_err(|e| Kind::InvalidHeight.context(e))?;

        // Collect all proofs as required
        let connection_proof =
            CommitmentProof::from(self.proven_connection(&connection_id, query_height)?.1);

        let mut client_state = None;
        let mut client_proof = None;
        let mut consensus_proof = None;

        match message_type {
            ConnectionMsgType::OpenTry | ConnectionMsgType::OpenAck => {
                let (client_state_value, client_state_proof) =
                    self.proven_client_state(&client_id, query_height)?;

                client_proof = Option::from(CommitmentProof::from(client_state_proof));

                let consensus_state_proof = self
                    .proven_client_consensus(
                        &client_id,
                        client_state_value.latest_height(),
                        query_height,
                    )?
                    .1;

                consensus_proof = Option::from(
                    ConsensusProof::new(
                        CommitmentProof::from(consensus_state_proof),
                        client_state_value.latest_height(),
                    )
                    .map_err(|e| {
                        Kind::ConnOpenTry(
                            connection_id.clone(),
                            "failed to build consensus proof".to_string(),
                        )
                        .context(e)
                    })?,
                );

                client_state = Option::from(client_state_value);
            }
            _ => {}
        }

        Ok((
            client_state,
            Proofs::new(connection_proof, client_proof, consensus_proof, height)
                .map_err(|_| Kind::MalformedProof)?,
        ))
    }
}
