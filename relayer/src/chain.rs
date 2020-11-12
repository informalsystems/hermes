pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;

pub mod handle;
pub mod runtime;

use std::convert::{TryFrom, TryInto};
use std::time::Duration;

use anomaly::fail;
use prost_types::Any;
use serde::{de::DeserializeOwned, Serialize};

use tendermint_proto::DomainType;

// TODO - tendermint deps should not be here
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint_light_client::types::TrustThreshold;
use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics03_connection::connection::{ConnectionEnd, Counterparty, State};
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::msgs::ConnectionMsgType;
use ibc::ics03_connection::version::get_compatible_versions;
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof};
use ibc::ics24_host::identifier::ChainId;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics24_host::Path;
use ibc::ics24_host::Path::ClientConsensusState as ClientConsensusPath;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::tx_msg::Msg;
use ibc::Height as ICSHeight;
use ibc::{
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics23_commitment::merkle::MerkleProof,
};

use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::light_client::LightClient;
use crate::tx::connection::{ConnectionOpenInitOptions, ConnectionOpenTryOptions};
use crate::util::block_on;

/// Generic query response type
/// TODO - will slowly move to GRPC protobuf specs for queries
pub struct QueryResponse {
    pub value: Vec<u8>,
    pub proof: MerkleProof,
    pub height: Height,
}

/// Defines a blockchain as understood by the relayer
pub trait Chain {
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync;

    /// Type of headers for this chain
    type Header: Header;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState;

    /// Type of the client state for this chain
    type ClientState: ClientState;

    /// Type of RPC requester (wrapper around low-level RPC client) for this chain
    type RpcClient: RpcClient + Send + Sync;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        &self.config().id
    }

    /// Returns the chain's configuration
    fn config(&self) -> &ChainConfig;

    /// Get a low-level RPC client for this chain
    /// TODO - Should this be part of the Chain trait?
    fn rpc_client(&self) -> &Self::RpcClient;

    /// Perform a generic ICS `query`, and return the corresponding response data.
    fn query(&self, data: Path, height: ICSHeight, prove: bool) -> Result<QueryResponse, Error>;

    /// Send a transaction with `msgs` to chain.
    fn send(
        &mut self,
        proto_msgs: Vec<Any>,
        key: KeyEntry,
        memo: String,
        timeout_height: u64,
    ) -> Result<String, Error>;

    /// Get the key and account Id - temporary solution
    fn key_and_signer(&mut self, key_file_contents: &str) -> Result<(KeyEntry, AccountId), Error>;

    // Build states
    fn build_client_state(&self, height: ICSHeight) -> Result<Self::ClientState, Error>;

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error>;

    fn build_header(
        &self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
    ) -> Result<Self::Header, Error>;

    // Downcast methods
    fn downcast_header(&self, header: AnyHeader) -> Option<Self::Header>;
    fn downcast_client_state(&self, client_state: AnyClientState) -> Option<Self::ClientState>;
    fn downcast_consensus_state(
        &self,
        consensus_state: AnyConsensusState,
    ) -> Option<Self::ConsensusState>;

    // Queries

    /// Query the latest height the chain is at
    fn query_latest_height(&self) -> Result<ICSHeight, Error>;

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Self::ClientState, Error>;

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
            .query(Path::Connections(connection_id.clone()), height, false)
            .map_err(|e| Kind::Query.context(e))
            .and_then(|v| {
                ConnectionEnd::decode_vec(&v.value).map_err(|e| Kind::Query.context(e))
            })?)
    }

    // Provable queries

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Self::ClientState, MerkleProof), Error>;

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<(ConnectionEnd, MerkleProof), Error> {
        let res = self
            .query(Path::Connections(connection_id.clone()), height, true)
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
    ) -> Result<(Self::ConsensusState, MerkleProof), Error>;

    /// Build the required proofs for connection handshake messages. The proofs are obtained from
    /// queries at height - 1
    fn build_connection_proofs(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<Proofs, Error> {
        // Set the height of the queries at height - 1
        let query_height = height
            .decrement()
            .map_err(|e| Kind::InvalidHeight.context(e))?;

        let connection_proof =
            CommitmentProof::from(self.proven_connection(&connection_id, query_height)?.1);

        let mut client_proof: Option<CommitmentProof> = None;
        let mut consensus_proof = None;

        match message_type {
            ConnectionMsgType::OpenTry | ConnectionMsgType::OpenAck => {
                let (client_state, client_state_proof) =
                    self.proven_client_state(&client_id, query_height)?;

                client_proof = Some(CommitmentProof::from(client_state_proof));

                let consensus_state_proof = self
                    .proven_client_consensus(
                        &client_id,
                        client_state.latest_height(),
                        query_height,
                    )?
                    .1;

                consensus_proof = Some(
                    ConsensusProof::new(
                        CommitmentProof::from(consensus_state_proof),
                        client_state.latest_height(),
                    )
                    .map_err(|e| {
                        Kind::ConnOpenTry(
                            connection_id.clone(),
                            "failed to build consensus proof".to_string(),
                        )
                        .context(e)
                    })?,
                );
            }
            _ => {}
        }

        Ok(
            Proofs::new(connection_proof, client_proof, consensus_proof, height)
                .map_err(|e| Kind::MalformedProof)?,
        )
    }
}
