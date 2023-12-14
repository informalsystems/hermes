use core::fmt::{
    Display,
    Error as FmtError,
    Formatter,
};

use crossbeam_channel as channel;
use ibc_proto::ibc::apps::fee::v1::{
    QueryIncentivizedPacketRequest,
    QueryIncentivizedPacketResponse,
};
use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    core::{
        ics02_client::{
            events::UpdateClient,
            header::AnyHeader,
        },
        ics03_connection::{
            connection::{
                ConnectionEnd,
                IdentifiedConnectionEnd,
            },
            version::Version,
        },
        ics04_channel::{
            channel::{
                ChannelEnd,
                IdentifiedChannelEnd,
            },
            packet::{
                PacketMsgType,
                Sequence,
            },
        },
        ics23_commitment::{
            commitment::CommitmentPrefix,
            merkle::MerkleProof,
        },
        ics24_host::identifier::{
            ChainId,
            ChannelId,
            ClientId,
            ConnectionId,
            PortChannelId,
            PortId,
        },
    },
    proofs::Proofs,
    signer::Signer,
    Height,
};
use tracing::Span;

use crate::{
    account::Balance,
    cache::{
        Cache,
        CacheStatus,
    },
    chain::{
        client::ClientSettings,
        cosmos::version::Specs,
        endpoint::{
            ChainStatus,
            HealthCheck,
        },
        handle::{
            ChainHandle,
            ChainRequest,
            Subscription,
        },
        requests::*,
        tracking::TrackedMsgs,
    },
    client_state::{
        AnyClientState,
        IdentifiedAnyClientState,
    },
    config::ChainConfig,
    connection::ConnectionMsgType,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::IbcEventWithHeight,
    keyring::AnySigningKeyPair,
    misbehaviour::MisbehaviourEvidence,
    telemetry,
};

/// A chain handle with support for caching.
/// To be used for the passive relaying mode (i.e., `start` CLI).
#[derive(Debug, Clone)]
pub struct CachingChainHandle<Handle> {
    inner: Handle,
    cache: Cache,
}

impl<Handle> CachingChainHandle<Handle> {
    pub fn new(handle: Handle) -> Self {
        Self {
            inner: handle,
            cache: Cache::new(),
        }
    }

    fn inner(&self) -> &Handle {
        &self.inner
    }
}

impl<Handle: ChainHandle> Display for CachingChainHandle<Handle> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "CachingChainHandle {{ chain_id: {} }}",
            self.inner().id()
        )
    }
}

impl<Handle: ChainHandle> ChainHandle for CachingChainHandle<Handle> {
    fn new(chain_id: ChainId, sender: channel::Sender<(Span, ChainRequest)>) -> Self {
        Self::new(Handle::new(chain_id, sender))
    }

    fn id(&self) -> ChainId {
        self.inner().id()
    }

    fn shutdown(&self) -> Result<(), Error> {
        self.inner().shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        self.inner().health_check()
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        self.inner().subscribe()
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.inner().send_messages_and_wait_commit(tracked_msgs)
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        self.inner().send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.inner().get_signer()
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        self.inner().config()
    }

    fn get_key(&self) -> Result<AnySigningKeyPair, Error> {
        self.inner().get_key()
    }

    fn add_key(&self, key_name: String, key: AnySigningKeyPair) -> Result<(), Error> {
        self.inner().add_key(key_name, key)
    }

    fn version_specs(&self) -> Result<Specs, Error> {
        self.inner().version_specs()
    }

    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error> {
        self.inner().query_balance(key_name, denom)
    }

    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error> {
        self.inner().query_all_balances(key_name)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.inner().query_denom_trace(hash)
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        self.inner().query_application_status()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        let handle = self.inner();
        let (result, in_cache) = self
            .cache
            .get_or_try_update_latest_height_with(|| handle.query_latest_height())?;

        if in_cache == CacheStatus::Hit {
            telemetry!(queries_cache_hits, &self.id(), "query_latest_height");
        }

        Ok(result)
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        self.inner().query_clients(request)
    }

    // TODO: Introduce new query_client_state_latest to separate from this one.
    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        let handle = self.inner();
        match include_proof {
            IncludeProof::Yes => handle.query_client_state(request, IncludeProof::Yes),
            IncludeProof::No => {
                if matches!(request.height, QueryHeight::Latest) {
                    let (result, in_cache) = self.cache.get_or_try_insert_client_state_with(
                        &request.client_id,
                        || {
                            handle
                                .query_client_state(request.clone(), IncludeProof::No)
                                .map(|(client_state, _)| client_state)
                        },
                    )?;

                    if in_cache == CacheStatus::Hit {
                        telemetry!(queries_cache_hits, &self.id(), "query_client_state");
                    }

                    Ok((result, None))
                } else {
                    handle.query_client_state(request, IncludeProof::No)
                }
            }
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.inner().query_client_connections(request)
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<Height>, Error> {
        self.inner().query_consensus_state_heights(request)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.inner().query_consensus_state(request, include_proof)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.inner().query_upgraded_client_state(request)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.inner().query_upgraded_consensus_state(request)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.inner().query_commitment_prefix()
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        self.inner().query_compatible_versions()
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        let handle = self.inner();
        match include_proof {
            IncludeProof::Yes => handle.query_connection(request, IncludeProof::Yes),
            IncludeProof::No => {
                if matches!(request.height, QueryHeight::Latest) {
                    let (result, in_cache) = self.cache.get_or_try_insert_connection_with(
                        &request.connection_id,
                        || {
                            handle
                                .query_connection(request.clone(), IncludeProof::No)
                                .map(|(conn_end, _)| conn_end)
                        },
                    )?;

                    if in_cache == CacheStatus::Hit {
                        telemetry!(queries_cache_hits, &self.id(), "query_connection");
                    }

                    Ok((result, None))
                } else {
                    handle.query_connection(request, IncludeProof::No)
                }
            }
        }
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        self.inner().query_connections(request)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inner().query_connection_channels(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.inner()
            .query_next_sequence_receive(request, include_proof)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.inner().query_channels(request)
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        let handle = self.inner();
        match include_proof {
            IncludeProof::Yes => handle.query_channel(request, IncludeProof::Yes),
            IncludeProof::No => {
                if matches!(request.height, QueryHeight::Latest) {
                    let (result, in_cache) = self.cache.get_or_try_insert_channel_with(
                        &PortChannelId::new(request.channel_id.clone(), request.port_id.clone()),
                        || {
                            handle
                                .query_channel(request, IncludeProof::No)
                                .map(|(channel_end, _)| channel_end)
                        },
                    )?;

                    if in_cache == CacheStatus::Hit {
                        telemetry!(queries_cache_hits, &self.id(), "query_channel");
                    }

                    Ok((result, None))
                } else {
                    handle.query_channel(request, IncludeProof::No)
                }
            }
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.inner().query_channel_client_state(request)
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        self.inner()
            .build_header(trusted_height, target_height, client_state)
    }

    /// Constructs a client state at the given height
    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<AnyClientState, Error> {
        self.inner().build_client_state(height, settings)
    }

    /// Constructs a consensus state at the given height
    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        self.inner()
            .build_consensus_state(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &self,
        update: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.inner().check_misbehaviour(update, client_state)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        self.inner().build_connection_proofs_and_client_state(
            message_type,
            connection_id,
            client_id,
            height,
        )
    }

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.inner()
            .build_channel_proofs(port_id, channel_id, height)
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<Proofs, Error> {
        self.inner()
            .build_packet_proofs(packet_type, port_id, channel_id, sequence, height)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inner().query_packet_commitment(request, include_proof)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.inner().query_packet_commitments(request)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inner().query_packet_receipt(request, include_proof)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.inner().query_unreceived_packets(request)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.inner()
            .query_packet_acknowledgement(request, include_proof)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.inner().query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.inner().query_unreceived_acknowledgements(request)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.inner().query_txs(request)
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        self.inner().query_packet_events(request)
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        self.inner.query_host_consensus_state(request)
    }

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error> {
        self.inner
            .maybe_register_counterparty_payee(channel_id, port_id, counterparty_payee)
    }

    fn cross_chain_query(
        &self,
        request: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        self.inner.cross_chain_query(request)
    }

    fn query_incentivized_packet(
        &self,
        request: QueryIncentivizedPacketRequest,
    ) -> Result<QueryIncentivizedPacketResponse, Error> {
        self.inner.query_incentivized_packet(request)
    }

    fn query_consumer_chains(&self) -> Result<Vec<(ChainId, ClientId)>, Error> {
        self.inner.query_consumer_chains()
    }
}
