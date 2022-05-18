use alloc::sync::Arc;
use core::convert::TryFrom;
use ibc::core::ics23_commitment::merkle::MerkleProof;

use tokio::runtime::Runtime as TokioRuntime;

pub use cosmos::CosmosSdkChain;

use ibc::core::ics02_client::client_consensus::{
    AnyConsensusState, AnyConsensusStateWithHeight, ConsensusState,
};
use ibc::core::ics02_client::client_state::{
    AnyClientState, ClientState, IdentifiedAnyClientState,
};
use ibc::core::ics02_client::header::Header;
use ibc::core::ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd, State};
use ibc::core::ics03_connection::version::{get_compatible_versions, Version};
use ibc::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::core::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::events::IbcEvent;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::query::{QueryBlockRequest, QueryTxRequest};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height as ICSHeight;
use tendermint::block::Height;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response as TxResponse;

use crate::account::Balance;
use crate::config::ChainConfig;
use crate::connection::ConnectionMsgType;
use crate::error::Error;
use crate::event::monitor::{EventReceiver, TxMonitorCmd};
use crate::keyring::{KeyEntry, KeyRing};
use crate::light_client::LightClient;

use self::client::ClientSettings;
use self::requests::{
    QueryChannelClientStateRequest, QueryChannelRequest, QueryChannelsRequest,
    QueryClientConnectionsRequest, QueryClientStateRequest, QueryClientStatesRequest,
    QueryConnectionChannelsRequest, QueryConnectionRequest, QueryConnectionsRequest,
    QueryConsensusStateRequest, QueryConsensusStatesRequest, QueryHostConsensusStateRequest,
    QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
    QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
};
use self::tracking::TrackedMsgs;

pub mod client;
pub mod cosmos;
pub mod counterparty;
pub mod handle;
pub mod requests;
pub mod runtime;
pub mod tracking;

#[cfg(test)]
pub mod mock;

/// The result of a health check.
#[derive(Debug)]
pub enum HealthCheck {
    Healthy,
    Unhealthy(Box<Error>),
}

/// The result of the application status query.
#[derive(Clone, Debug)]
pub struct ChainStatus {
    pub height: ICSHeight,
    pub timestamp: Timestamp,
}

/// Generic query response type
/// TODO - will slowly move to GRPC protobuf specs for queries
#[derive(Clone, Debug, PartialEq)]
pub struct QueryResponse {
    pub value: Vec<u8>,
    pub proof: Option<MerkleProof>,
    pub height: Height,
}

/// Defines a blockchain as understood by the relayer
pub trait ChainEndpoint: Sized {
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync;

    /// Type of headers for this chain
    type Header: Header;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState;

    /// Type of the client state for this chain
    type ClientState: ClientState;

    type LightClient: LightClient<Self>;

    /// Constructs the chain
    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error>;

    #[allow(clippy::type_complexity)]
    /// Initializes and returns the light client (if any) associated with this chain.
    fn init_light_client(&self) -> Result<Self::LightClient, Error>;

    /// Initializes and returns the event monitor (if any) associated with this chain.
    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error>;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId;

    /// Shutdown the chain runtime
    fn shutdown(self) -> Result<(), Error>;

    /// Perform a health check
    fn health_check(&self) -> Result<HealthCheck, Error>;

    /// Returns the chain's keybase
    fn keybase(&self) -> &KeyRing;

    /// Returns the chain's keybase, mutably
    fn keybase_mut(&mut self) -> &mut KeyRing;

    /// Sends one or more transactions with `msgs` to chain and
    /// synchronously wait for it to be committed.
    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error>;

    /// Sends one or more transactions with `msgs` to chain.
    /// Non-blocking alternative to `send_messages_and_wait_commit` interface.
    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<TxResponse>, Error>;

    fn get_signer(&mut self) -> Result<Signer, Error>;

    fn config(&self) -> ChainConfig;

    fn get_key(&mut self) -> Result<KeyEntry, Error>;

    fn add_key(&mut self, key_name: &str, key: KeyEntry) -> Result<(), Error>;

    /// Return the version of the IBC protocol that this chain is running, if known.
    fn ibc_version(&self) -> Result<Option<semver::Version>, Error>;

    // Queries

    /// Query the balance of the current account for the denom used to pay tx fees.
    fn query_balance(&self) -> Result<Balance, Error>;

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error>;

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        // TODO - do a real chain query
        Ok(get_compatible_versions())
    }

    /// Query the latest height and timestamp the application is at
    fn query_application_status(&self) -> Result<ChainStatus, Error>;

    /// Performs a query to retrieve the state of all clients that a chain hosts.
    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error>;

    fn query_client_state(&self, request: QueryClientStateRequest)
        -> Result<AnyClientState, Error>;

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error>;

    /// Performs a query to retrieve the consensus state (for a specific height `consensus_height`)
    /// that an on-chain client stores.
    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error>;

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error>;

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error>;

    /// Performs a query to retrieve the identifiers of all connections.
    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error>;

    fn query_connection(&self, request: QueryConnectionRequest) -> Result<ConnectionEnd, Error>;

    /// Performs a query to retrieve the identifiers of all channels associated with a connection.
    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    /// Performs a query to retrieve the identifiers of all channels.
    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    fn query_channel(&self, request: QueryChannelRequest) -> Result<ChannelEnd, Error>;

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error>;

    /// Queries all the packet commitments hashes associated with a channel.
    /// Returns the corresponding packet sequence numbers.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error>;

    /// Queries all the unreceived IBC packets associated with a channel and packet commit sequences.
    /// Returns the corresponding packet sequence numbers.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error>;

    /// Queries all the packet acknowledgements associated with a channel.
    /// Returns the corresponding packet sequence numbers.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error>;

    /// Queries all the unreceived packet acknowledgements associated with a
    /// Returns the corresponding packet sequence numbers.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error>;

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
    ) -> Result<Sequence, Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error>;

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error>;

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error>;

    // Provable queries
    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(AnyClientState, MerkleProof), Error>;

    fn proven_connection(
        &self,
        connection_id: &ConnectionId,
        height: ICSHeight,
    ) -> Result<(ConnectionEnd, MerkleProof), Error>;

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: ICSHeight,
        height: ICSHeight,
    ) -> Result<(AnyConsensusState, MerkleProof), Error>;

    fn proven_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<(ChannelEnd, MerkleProof), Error>;

    fn proven_packet(
        &self,
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: ICSHeight,
    ) -> Result<(Vec<u8>, MerkleProof), Error>;

    fn build_client_state(
        &self,
        height: ICSHeight,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error>;

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error>;

    /// Fetch, and verify the header at `target_height`, assuming we trust the
    /// header at `trusted_height` with the given `client_state`.
    ///
    /// Returns all the supporting headers that were need to verify the target
    /// header, for use when building a `ClientUpdate` message.
    fn build_header(
        &self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
        light_client: &mut Self::LightClient,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error>;

    /// Builds the required proofs and the client state for connection handshake messages.
    /// The proofs and client state must be obtained from queries at same height.
    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: ICSHeight,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        let (connection_end, connection_proof) = self.proven_connection(connection_id, height)?;

        // Check that the connection state is compatible with the message
        match message_type {
            ConnectionMsgType::OpenTry => {
                if !connection_end.state_matches(&State::Init)
                    && !connection_end.state_matches(&State::TryOpen)
                {
                    return Err(Error::bad_connection_state());
                }
            }
            ConnectionMsgType::OpenAck => {
                if !connection_end.state_matches(&State::TryOpen)
                    && !connection_end.state_matches(&State::Open)
                {
                    return Err(Error::bad_connection_state());
                }
            }
            ConnectionMsgType::OpenConfirm => {
                if !connection_end.state_matches(&State::Open) {
                    return Err(Error::bad_connection_state());
                }
            }
        }

        let mut client_state = None;
        let mut client_proof = None;
        let mut consensus_proof = None;

        match message_type {
            ConnectionMsgType::OpenTry | ConnectionMsgType::OpenAck => {
                let (client_state_value, client_state_proof) =
                    self.proven_client_state(client_id, height)?;

                client_proof = Some(
                    CommitmentProofBytes::try_from(client_state_proof)
                        .map_err(Error::malformed_proof)?,
                );

                let consensus_state_proof = self
                    .proven_client_consensus(client_id, client_state_value.latest_height(), height)?
                    .1;

                consensus_proof = Option::from(
                    ConsensusProof::new(
                        CommitmentProofBytes::try_from(consensus_state_proof)
                            .map_err(Error::malformed_proof)?,
                        client_state_value.latest_height(),
                    )
                    .map_err(Error::consensus_proof)?,
                );

                client_state = Some(client_state_value);
            }
            _ => {}
        }

        Ok((
            client_state,
            Proofs::new(
                CommitmentProofBytes::try_from(connection_proof).map_err(Error::malformed_proof)?,
                client_proof,
                consensus_proof,
                None,
                height.increment(),
            )
            .map_err(Error::malformed_proof)?,
        ))
    }

    /// Builds the proof for channel handshake messages.
    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: ICSHeight,
    ) -> Result<Proofs, Error> {
        // Collect all proofs as required
        let channel_proof =
            CommitmentProofBytes::try_from(self.proven_channel(port_id, channel_id, height)?.1)
                .map_err(Error::malformed_proof)?;

        Proofs::new(channel_proof, None, None, None, height.increment())
            .map_err(Error::malformed_proof)
    }

    /// Builds the proof for packet messages.
    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: ICSHeight,
    ) -> Result<(Vec<u8>, Proofs), Error> {
        let channel_proof = if packet_type == PacketMsgType::TimeoutOnClose {
            Some(
                CommitmentProofBytes::try_from(
                    self.proven_channel(&port_id, &channel_id, height)?.1,
                )
                .map_err(Error::malformed_proof)?,
            )
        } else {
            None
        };

        let (bytes, packet_proof) =
            self.proven_packet(packet_type, port_id, channel_id, sequence, height)?;

        let proofs = Proofs::new(
            CommitmentProofBytes::try_from(packet_proof).map_err(Error::malformed_proof)?,
            None,
            None,
            channel_proof,
            height.increment(),
        )
        .map_err(Error::malformed_proof)?;

        Ok((bytes, proofs))
    }
}
