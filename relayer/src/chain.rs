use std::{sync::Arc, thread};

use crossbeam_channel as channel;
use prost_types::Any;
// TODO - tendermint deps should not be here
use tendermint::account::Id as AccountId;
use tendermint::block::Height;
use tendermint_proto::Protobuf;
use tokio::runtime::Runtime as TokioRuntime;

pub use cosmos::CosmosSDKChain;
use ibc::events::IBCEvent;
use ibc::ics02_client::header::Header;
use ibc::ics02_client::state::{ClientState, ConsensusState};
use ibc::ics03_connection::connection::{ConnectionEnd, State};
use ibc::ics03_connection::raw::ConnectionIds;
use ibc::ics03_connection::version::{get_compatible_versions, Version};
use ibc::ics04_channel::channel::{ChannelEnd, QueryPacketEventDataRequest};
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::ics24_host::Path;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::Height as ICSHeight;
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryConnectionChannelsRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::ibc::core::connection::v1::QueryConnectionsRequest;

use crate::config::ChainConfig;
use crate::connection::ConnectionMsgType;
use crate::error::{Error, Kind};
use crate::event::monitor::EventBatch;
use crate::keyring::store::{KeyEntry, KeyRing};
use crate::light_client::LightClient;

pub(crate) mod cosmos;
pub mod handle;
pub mod runtime;

#[cfg(test)]
pub mod mock;

/// Generic query response type
/// TODO - will slowly move to GRPC protobuf specs for queries
#[derive(Clone, Debug, PartialEq)]
pub struct QueryResponse {
    pub value: Vec<u8>,
    pub proof: Option<MerkleProof>,
    pub height: Height,
}

/// Packet query options
#[derive(Debug)]
pub struct QueryPacketOptions {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub height: u64,
}

/// Defines a blockchain as understood by the relayer
pub trait Chain: Sized {
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync;

    /// Type of headers for this chain
    type Header: Header;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState;

    /// Type of the client state for this chain
    type ClientState: ClientState;

    /// Constructs the chain
    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error>;

    #[allow(clippy::type_complexity)]
    /// Initializes and returns the light client (if any) associated with this chain.
    fn init_light_client(
        &self,
    ) -> Result<(Box<dyn LightClient<Self>>, Option<thread::JoinHandle<()>>), Error>;

    /// Initializes and returns the event monitor (if any) associated with this chain.
    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<
        (
            channel::Receiver<EventBatch>,
            Option<thread::JoinHandle<()>>,
        ),
        Error,
    >;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId;

    /// Returns the chain's keybase
    fn keybase(&self) -> &KeyRing;

    /// Perform a generic ICS `query`, and return the corresponding response data.
    fn query(&self, data: Path, height: ICSHeight, prove: bool) -> Result<QueryResponse, Error>;

    /// Sends one or more transactions with `msgs` to chain.
    fn send_msgs(&mut self, proto_msgs: Vec<Any>) -> Result<Vec<IBCEvent>, Error>;

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

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        // TODO - do a real chain query
        Ok(get_compatible_versions())
    }

    fn query_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<ConnectionEnd, Error> {
        let res = self.query(Path::Connections(connection_id.clone()), height, false)?;
        Ok(ConnectionEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("connection".into()).context(e))?)
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
        Ok(ChannelEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("channel".into()).context(e))?)
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
            .map_err(|e| Kind::Query("proven connection".into()).context(e))?;
        let connection_end = ConnectionEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("proven connection".into()).context(e))?;

        Ok((
            connection_end,
            res.proof.ok_or_else(|| {
                Kind::Query("proven connection".into()).context("empty proof".to_string())
            })?,
        ))
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
            .map_err(|e| Kind::Query("proven channel".into()).context(e))?;

        let channel_end = ChannelEnd::decode_vec(&res.value)
            .map_err(|e| Kind::Query("proven channel".into()).context(e))?;

        Ok((
            channel_end,
            res.proof.ok_or_else(|| {
                Kind::Query("proven channel".into()).context("empty proof".to_string())
            })?,
        ))
    }

    /// Builds the required proofs and the client state for connection handshake messages.
    /// The proofs and client state must be obtained from queries at same height.
    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Option<Self::ClientState>, Proofs), Error> {
        let (connection_end, connection_proof) = self.proven_connection(&connection_id, height)?;

        // Check that the connection state is compatible with the message
        match message_type {
            ConnectionMsgType::OpenTry => {
                if !connection_end.state_matches(&State::Init)
                    && !connection_end.state_matches(&State::TryOpen)
                {
                    return Err(Kind::ConnOpenTry("bad connection state".to_string()).into());
                }
            }
            ConnectionMsgType::OpenAck => {
                if !connection_end.state_matches(&State::TryOpen)
                    && !connection_end.state_matches(&State::Open)
                {
                    return Err(Kind::ConnOpenTry("bad connection state".to_string()).into());
                }
            }
            ConnectionMsgType::OpenConfirm => {
                if !connection_end.state_matches(&State::Open) {
                    return Err(Kind::ConnOpenTry("bad connection state".to_string()).into());
                }
            }
        }

        let mut client_state = None;
        let mut client_proof = None;
        let mut consensus_proof = None;

        match message_type {
            ConnectionMsgType::OpenTry | ConnectionMsgType::OpenAck => {
                let (client_state_value, client_state_proof) =
                    self.proven_client_state(&client_id, height)?;

                client_proof = Some(CommitmentProofBytes::from(client_state_proof));

                let consensus_state_proof = self
                    .proven_client_consensus(
                        &client_id,
                        client_state_value.latest_height(),
                        height,
                    )?
                    .1;

                consensus_proof = Option::from(
                    ConsensusProof::new(
                        CommitmentProofBytes::from(consensus_state_proof),
                        client_state_value.latest_height(),
                    )
                    .map_err(|e| {
                        Kind::ConnOpenTry("failed to build consensus proof".to_string()).context(e)
                    })?,
                );

                client_state = Some(client_state_value);
            }
            _ => {}
        }

        Ok((
            client_state,
            Proofs::new(
                CommitmentProofBytes::from(connection_proof),
                client_proof,
                consensus_proof,
                height.increment(),
            )
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
    /// The proof is obtained from queries at height `height`
    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<Proofs, Error> {
        // Collect all proofs as required
        let channel_proof =
            CommitmentProofBytes::from(self.proven_channel(port_id, channel_id, height)?.1);

        Ok(Proofs::new(channel_proof, None, None, height.increment())
            .map_err(|_| Kind::MalformedProof)?)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error>;

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<u64>, Error>;

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<PacketState>, ICSHeight), Error>;

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<u64>, Error>;

    /// Performs a query to retrieve the identifiers of all channels associated with a connection.
    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<ChannelId>, Error>;

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_connections(&self, request: QueryConnectionsRequest) -> Result<ConnectionIds, Error>;

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: ICSHeight,
    ) -> Result<(Vec<u8>, Proofs), Error> {
        let data: Path;
        match packet_type {
            PacketMsgType::Recv => {
                data = Path::Commitments {
                    port_id: port_id.clone(),
                    channel_id: channel_id.clone(),
                    sequence,
                }
            }
            PacketMsgType::Ack => {
                data = Path::Acks {
                    port_id: port_id.clone(),
                    channel_id: channel_id.clone(),
                    sequence,
                }
            }
            PacketMsgType::Timeout => {
                data = Path::Receipts {
                    port_id: port_id.clone(),
                    channel_id: channel_id.clone(),
                    sequence,
                }
            }
        }

        let res = self
            .query(data, height, true)
            .map_err(|e| Kind::Query(packet_type.to_string()).context(e))?;

        let proofs = Proofs::new(
            CommitmentProofBytes::from(res.proof.ok_or_else(|| {
                Kind::Query(packet_type.to_string()).context("empty proof".to_string())
            })?),
            None,
            None,
            height.increment(),
        )
        .map_err(|_| Kind::MalformedProof)?;

        Ok((res.value, proofs))
    }

    fn query_txs(&self, request: QueryPacketEventDataRequest) -> Result<Vec<IBCEvent>, Error>;
}
