use alloc::sync::Arc;
use core::convert::TryFrom;

use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics02_client::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics02_client::events::UpdateClient;
use ibc_relayer_types::core::ics02_client::header::Header;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd, State,
};
use ibc_relayer_types::core::ics03_connection::version::{get_compatible_versions, Version};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc_relayer_types::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes,
};
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::core::ics24_host::identifier::{
    ChainId, ChannelId, ClientId, ConnectionId, PortId,
};
use ibc_relayer_types::proofs::{ConsensusProof, Proofs};
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::Height as ICSHeight;

use tendermint_rpc::endpoint::broadcast::tx_sync::Response as TxResponse;

use crate::account::Balance;
use crate::chain::client::ClientSettings;
use crate::chain::requests::*;
use crate::chain::tracking::TrackedMsgs;
use crate::client_state::{AnyClientState, IdentifiedAnyClientState};
use crate::config::ChainConfig;
use crate::connection::ConnectionMsgType;
use crate::consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight};
use crate::denom::DenomTrace;
use crate::error::{Error, QUERY_PROOF_EXPECT_MSG};
use crate::event::monitor::{EventReceiver, TxMonitorCmd};
use crate::event::IbcEventWithHeight;
use crate::keyring::{KeyEntry, KeyRing};
use crate::light_client::AnyHeader;
use crate::misbehaviour::MisbehaviourEvidence;

use super::requests::{
    IncludeProof, QueryHeight, QueryPacketAcknowledgementRequest, QueryPacketCommitmentRequest,
    QueryPacketReceiptRequest, QueryTxRequest,
};

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

/// Defines a blockchain as understood by the relayer
pub trait ChainEndpoint: Sized {
    /// Type of light blocks for this chain
    type LightBlock: Send + Sync;

    /// Type of headers for this chain
    type Header: Header + Into<AnyHeader>;

    /// Type of consensus state for this chain
    type ConsensusState: ConsensusState + Into<AnyConsensusState>;

    /// Type of the client state for this chain
    type ClientState: ClientState + Into<AnyClientState>;

    /// Returns the chain's identifier
    fn id(&self) -> &ChainId {
        &self.config().id
    }

    /// Returns the chain configuration
    fn config(&self) -> &ChainConfig;

    // Life cycle

    /// Constructs the chain
    fn bootstrap(config: ChainConfig, rt: Arc<TokioRuntime>) -> Result<Self, Error>;

    /// Initializes and returns the event monitor (if any) associated with this chain.
    fn init_event_monitor(
        &self,
        rt: Arc<TokioRuntime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error>;

    /// Shutdown the chain runtime
    fn shutdown(self) -> Result<(), Error>;

    /// Perform a health check
    fn health_check(&self) -> Result<HealthCheck, Error>;

    // Keyring

    /// Returns the chain's keybase
    fn keybase(&self) -> &KeyRing;

    /// Returns the chain's keybase, mutably
    fn keybase_mut(&mut self) -> &mut KeyRing;

    fn get_signer(&self) -> Result<Signer, Error>;

    /// Get the signing key
    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        crate::time!("get_key");

        // Get the key from key seed file
        let key = self
            .keybase()
            .get_key(&self.config().key_name)
            .map_err(|e| Error::key_not_found(self.config().key_name.clone(), e))?;

        Ok(key)
    }

    fn add_key(&mut self, key_name: &str, key: KeyEntry) -> Result<(), Error> {
        self.keybase_mut()
            .add_key(key_name, key)
            .map_err(Error::key_base)?;

        Ok(())
    }

    // Versioning

    /// Return the version of the IBC protocol that this chain is running, if known.
    fn ibc_version(&self) -> Result<Option<semver::Version>, Error>;

    // Send transactions

    /// Sends one or more transactions with `msgs` to chain and
    /// synchronously wait for it to be committed.
    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error>;

    /// Sends one or more transactions with `msgs` to chain.
    /// Non-blocking alternative to `send_messages_and_wait_commit` interface.
    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<TxResponse>, Error>;

    /// Fetch a header from the chain at the given height and verify it.
    fn verify_header(
        &mut self,
        trusted: ICSHeight,
        target: ICSHeight,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error>;

    /// Given a client update event that includes the header used in a client update,
    /// look for misbehaviour by fetching a header at same or latest height.
    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error>;

    // Queries

    /// Query the balance of the given account for the given denom.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    /// If no denom is given, behavior must be specified, e.g. retrieve the denom used to pay tx fees.
    fn query_balance(&self, key_name: Option<&str>, denom: Option<&str>) -> Result<Balance, Error>;

    /// Query the balances of the given account for all the denom.
    /// If no account is given, behavior must be specified, e.g. retrieve it from configuration file.
    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error>;

    /// Query the denomination trace given a trace hash.
    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error>;

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

    /// Performs a query to retrieve the state of the specified light client. A
    /// proof can optionally be returned along with the result.
    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve the consensus state for a specified height
    /// `consensus_height` that the specified light client stores.
    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the consensus states that the specified
    /// light client stores.
    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error>;

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

    /// Performs a query to retrieve the connection associated with a given
    /// connection identifier. A proof can optionally be returned along with the
    /// result.
    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all channels associated with a connection.
    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    /// Performs a query to retrieve all the channels of a chain.
    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error>;

    /// Performs a query to retrieve the channel associated with a given channel
    /// identifier. A proof can optionally be returned along with the result.
    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve the client state for the channel associated
    /// with a given channel identifier.
    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error>;

    /// Performs a query to retrieve a stored packet commitment hash, stored on
    /// the chain at path `path::CommitmentsPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the packet commitments hashes
    /// associated with a channel. Returns the corresponding packet sequence
    /// numbers and the height at which they were retrieved.
    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error>;

    /// Performs a query to retrieve a given packet receipt, stored on the chain at path
    /// `path::CommitmentsPath`. A proof can optionally be returned along with the result.
    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query about which IBC packets in the specified list has not
    /// been received. Returns the sequence numbers of the packets that were not
    /// received.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were received,
    /// while packets 7, 8 were not.
    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error>;

    /// Performs a query to retrieve a stored packet acknowledgement hash,
    /// stored on the chain at path `path::AcksPath`. A proof can optionally be
    /// returned along with the result.
    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error>;

    /// Performs a query to retrieve all the packet acknowledgements associated
    /// with a channel. Returns the corresponding packet sequence numbers and
    /// the height at which they were retrieved.
    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, ICSHeight), Error>;

    /// Performs a query about which IBC packets in the specified list has not
    /// been acknowledged. Returns the sequence numbers of the packets that were not
    /// acknowledged.
    ///
    /// For example, given a request with the sequence numbers `[5,6,7,8]`, a
    /// response of `[7,8]` would indicate that packets 5 & 6 were acknowledged,
    /// while packets 7, 8 were not.
    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error>;

    /// Performs a query to retrieve `nextSequenceRecv` stored at path
    /// `path::SeqRecvsPath` as defined in ICS-4. A proof can optionally be
    /// returned along with the result.
    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error>;

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error>;

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error>;

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error>;

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
        &mut self,
        trusted_height: ICSHeight,
        target_height: ICSHeight,
        client_state: &AnyClientState,
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
        let (connection_end, maybe_connection_proof) = self.query_connection(
            QueryConnectionRequest {
                connection_id: connection_id.clone(),
                height: QueryHeight::Specific(height),
            },
            IncludeProof::Yes,
        )?;
        let connection_proof = maybe_connection_proof.expect(QUERY_PROOF_EXPECT_MSG);

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
                let (client_state_value, maybe_client_state_proof) = self.query_client_state(
                    QueryClientStateRequest {
                        client_id: client_id.clone(),
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;
                let client_state_proof = maybe_client_state_proof.expect(QUERY_PROOF_EXPECT_MSG);

                client_proof = Some(
                    CommitmentProofBytes::try_from(client_state_proof)
                        .map_err(Error::malformed_proof)?,
                );

                let consensus_state_proof = {
                    let (_, maybe_consensus_state_proof) = self.query_consensus_state(
                        QueryConsensusStateRequest {
                            client_id: client_id.clone(),
                            consensus_height: client_state_value.latest_height(),
                            query_height: QueryHeight::Specific(height),
                        },
                        IncludeProof::Yes,
                    )?;

                    maybe_consensus_state_proof.expect(QUERY_PROOF_EXPECT_MSG)
                };

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
        let (_, maybe_channel_proof) = self.query_channel(
            QueryChannelRequest {
                port_id: port_id.clone(),
                channel_id: channel_id.clone(),
                height: QueryHeight::Specific(height),
            },
            IncludeProof::Yes,
        )?;
        let channel_proof = maybe_channel_proof.expect(QUERY_PROOF_EXPECT_MSG);
        let channel_proof_bytes =
            CommitmentProofBytes::try_from(channel_proof).map_err(Error::malformed_proof)?;

        Proofs::new(channel_proof_bytes, None, None, None, height.increment())
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
    ) -> Result<Proofs, Error> {
        let (maybe_packet_proof, channel_proof) = match packet_type {
            PacketMsgType::Recv => {
                let (_, maybe_packet_proof) = self.query_packet_commitment(
                    QueryPacketCommitmentRequest {
                        port_id,
                        channel_id,
                        sequence,
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;

                (maybe_packet_proof, None)
            }
            PacketMsgType::Ack => {
                let (_, maybe_packet_proof) = self.query_packet_acknowledgement(
                    QueryPacketAcknowledgementRequest {
                        port_id,
                        channel_id,
                        sequence,
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;

                (maybe_packet_proof, None)
            }
            PacketMsgType::TimeoutUnordered => {
                let (_, maybe_packet_proof) = self.query_packet_receipt(
                    QueryPacketReceiptRequest {
                        port_id,
                        channel_id,
                        sequence,
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;

                (maybe_packet_proof, None)
            }
            PacketMsgType::TimeoutOrdered => {
                let (_, maybe_packet_proof) = self.query_next_sequence_receive(
                    QueryNextSequenceReceiveRequest {
                        port_id,
                        channel_id,
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;

                (maybe_packet_proof, None)
            }
            PacketMsgType::TimeoutOnClose => {
                let channel_proof = {
                    let (_, maybe_channel_proof) = self.query_channel(
                        QueryChannelRequest {
                            port_id: port_id.clone(),
                            channel_id: channel_id.clone(),
                            height: QueryHeight::Specific(height),
                        },
                        IncludeProof::Yes,
                    )?;
                    let channel_merkle_proof = maybe_channel_proof.expect(QUERY_PROOF_EXPECT_MSG);
                    Some(
                        CommitmentProofBytes::try_from(channel_merkle_proof)
                            .map_err(Error::malformed_proof)?,
                    )
                };
                let (_, maybe_packet_proof) = self.query_packet_receipt(
                    QueryPacketReceiptRequest {
                        port_id,
                        channel_id,
                        sequence,
                        height: QueryHeight::Specific(height),
                    },
                    IncludeProof::Yes,
                )?;

                (maybe_packet_proof, channel_proof)
            }
        };

        let packet_proof = maybe_packet_proof.expect(QUERY_PROOF_EXPECT_MSG);

        let proofs = Proofs::new(
            CommitmentProofBytes::try_from(packet_proof).map_err(Error::malformed_proof)?,
            None,
            None,
            channel_proof,
            height.increment(),
        )
        .map_err(Error::malformed_proof)?;

        Ok(proofs)
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_payee: &Signer,
    ) -> Result<(), Error>;
}
