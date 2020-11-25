pub(crate) mod cosmos;
pub use cosmos::CosmosSDKChain;

pub mod handle;
pub mod runtime;

use prost_types::Any;

use tendermint_proto::Protobuf;

// TODO - tendermint deps should not be here
use tendermint::account::Id as AccountId;
use tendermint::block::Height;

use tendermint_rpc::Client as RpcClient;

use ibc::ics02_client::header::Header;

use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics03_connection::connection::ConnectionEnd;

use ibc::ics03_connection::version::get_compatible_versions;
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof};
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::ics24_host::Path;

use ibc::proofs::{ConsensusProof, Proofs};

use ibc::ics04_channel::channel::ChannelEnd;
use ibc::ics23_commitment::merkle::MerkleProof;
use ibc::Height as ICSHeight;

use crate::config::ChainConfig;
use crate::connection::ConnectionMsgType;
use crate::error::{Error, Kind};
use crate::keyring::store::{KeyEntry, KeyRing};

/// Generic query response type
/// TODO - will slowly move to GRPC protobuf specs for queries
#[derive(Clone, Debug, PartialEq)]
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

    /// Returns the chain's keybase
    fn keybase(&self) -> &KeyRing;

    /// Get a low-level RPC client for this chain
    /// TODO - Should this be part of the Chain trait?
    fn rpc_client(&self) -> &Self::RpcClient;

    /// Perform a generic ICS `query`, and return the corresponding response data.
    fn query(&self, data: Path, height: ICSHeight, prove: bool) -> Result<QueryResponse, Error>;

    /// Send a transaction with `msgs` to chain.
    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<String, Error>;

    fn get_signer(&mut self) -> Result<AccountId, Error>;

    fn get_key(&mut self) -> Result<KeyEntry, Error>;

    // Build states
    fn build_client_state(&self, height: ICSHeight) -> Result<Self::ClientState, Error>;

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error>;

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error>;

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
        let res = self.query(Path::Connections(connection_id.clone()), height, false)?;
        Ok(ConnectionEnd::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?)
    }

    fn query_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<ChannelEnd, Error> {
        let res = self.query(
            Path::ChannelEnds(port_id.clone(), channel_id.clone()),
            height,
            false,
        )?;
        Ok(ChannelEnd::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?)
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

    fn proven_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<(ChannelEnd, MerkleProof), Error> {
        let res = self
            .query(
                Path::ChannelEnds(port_id.clone(), channel_id.clone()),
                height,
                true,
            )
            .map_err(|e| Kind::Query.context(e))?;

        let channel_end = ChannelEnd::decode_vec(&res.value).map_err(|e| Kind::Query.context(e))?;

        Ok((channel_end, res.proof))
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
    ) -> Result<(Option<Self::ClientState>, Proofs), Error> {
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

                client_proof = Some(CommitmentProof::from(client_state_proof));

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

                client_state = Some(client_state_value);
            }
            _ => {}
        }

        Ok((
            client_state,
            Proofs::new(connection_proof, client_proof, consensus_proof, height)
                .map_err(|_| Kind::MalformedProof)?,
        ))
    }

    // TODO: Introduce a newtype for the module version string
    fn module_version(&self, port_id: &PortId) -> String {
        // TODO - query the chain, currently hardcoded
        if port_id.as_str() == "transfer" {
            "ics20-1".to_string()
        } else {
            "".to_string()
        }
    }

    /// Builds the proof for channel handshake messages.
    /// The proof must be obtained from queries at height `height - 1`
    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<Proofs, Error> {
        // Set the height of the queries at height - 1
        let query_height = height
            .decrement()
            .map_err(|e| Kind::InvalidHeight.context(e))?;

        // Collect all proofs as required
        let channel_proof =
            CommitmentProof::from(self.proven_channel(port_id, channel_id, query_height)?.1);

        Ok(Proofs::new(channel_proof, None, None, height).map_err(|_| Kind::MalformedProof)?)
    }
}
