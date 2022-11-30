#![allow(unused_variables, dead_code)]

use alloc::sync::Arc;
use core::future::Future;
use std::{borrow::Cow, collections::HashMap};

use semver::Version;
use sqlx::{postgres::PgPoolOptions, PgPool};
use tonic::metadata::AsciiMetadataValue;
use tracing::{debug, info, span, trace, warn, Level};

use tendermint::block;
use tendermint_rpc::{endpoint::broadcast::tx_sync, Client};

use ibc_relayer_types::{
    core::{
        ics02_client::events::{CreateClient, NewBlock, UpdateClient},
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::Sequence,
        },
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::{
            ChainId, ChannelId, ClientId, ConnectionId, PortChannelId, PortId,
        },
    },
    downcast,
    events::{IbcEvent, WithBlockDataType},
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    chain::{
        client::ClientSettings,
        cosmos::{query::account::get_or_fetch_account, CosmosSdkChain},
        endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
        handle::Subscription,
        psql_cosmos::{batch::send_batched_messages_and_wait_commit, query::*},
        requests::*,
        tracking::TrackedMsgs,
    },
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::{ChainConfig, SnapshotStoreType},
    consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight},
    denom::DenomTrace,
    error::Error,
    event::{monitor::EventBatch, IbcEventWithHeight},
    keyring::{KeyEntry, KeyRing},
    misbehaviour::MisbehaviourEvidence,
    snapshot::{
        memory::MemorySnapshotStore, psql::PsqlSnapshotStore, IbcData, IbcSnapshot, Key, PacketId,
        SnapshotStore,
    },
};

pub mod batch;
pub mod events;
pub mod query;
pub mod wait;

flex_error::define_error! {
    PsqlError {
        MissingConnectionConfig
            { chain_id: ChainId }
            |e| { format_args!("missing `psql_conn` config for chain '{}'", e.chain_id) },

        UnexpectedEvent
            { event: IbcEvent }
            |e| { format_args!("unexpected event '{}'", e.event) },

        ConnectionNotFound
            { connection_id: ConnectionId }
            |e| { format_args!("connection not found '{}'", e.connection_id) },

        ChannelNotFound
            { channel_id: ChannelId }
            |e| { format_args!("channel not found '{}'", e.channel_id) },

        ConsensusStateNotFound
            {
                client_id: ClientId,
                consensus_height: Height,
            }
            |e| { format_args!("consensus state for client '{}' at height {} not found", e.client_id, e.consensus_height) },

        ClientStateNotFound
            {
                client_id: ClientId,
                height: QueryHeight,
            }
            |e| { format_args!("client state for client '{}' at height {} not found", e.client_id, e.height) },
    }
}
#[derive(Eq, PartialEq)]
pub enum PsqlSyncStatus {
    Unknown,
    Synced,
}

pub struct PsqlChain {
    chain: CosmosSdkChain,
    pool: PgPool,
    snapshot_store: Box<dyn SnapshotStore>,
    rt: Arc<tokio::runtime::Runtime>,
    sync_state: PsqlSyncStatus,
}

impl PsqlChain {
    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    pub fn is_synced(&self) -> bool {
        self.sync_state == PsqlSyncStatus::Synced
    }

    async fn do_send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!("do_send_messages_and_wait_commit");

        let _span =
            span!(Level::DEBUG, "do_send_messages_and_wait_commit", id = %tracked_msgs.tracking_id()).entered();

        let proto_msgs = tracked_msgs.msgs;

        let key_entry = self.chain.key()?;

        let account = get_or_fetch_account(
            &self.chain.grpc_addr,
            &key_entry.account,
            &mut self.chain.account,
        )
        .await?;

        send_batched_messages_and_wait_commit(
            // TODO - look into moving some chain. members to self
            &self.pool,
            &self.chain.tx_config,
            self.chain.config.max_msg_num,
            self.chain.config.max_tx_size,
            &key_entry,
            account,
            &self.chain.config.memo_prefix,
            proto_msgs,
        )
        .await
    }

    #[tracing::instrument(skip_all)]
    fn populate_clients_and_consensus_states(
        &self,
        query_height: &QueryHeight,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        let request = QueryClientStatesRequest { pagination: None };
        self.populate_clients(query_height, request, snapshot)?;

        let client_ids = snapshot
            .data
            .client_states
            .keys()
            .cloned()
            .collect::<Vec<_>>();

        for client_id in client_ids {
            let request = QueryConsensusStatesRequest {
                client_id,
                pagination: None,
            };

            self.populate_consensus_states(query_height, request, snapshot)?;
        }

        Ok(())
    }

    #[tracing::instrument(skip_all)]
    fn populate_clients(
        &self,
        query_height: &QueryHeight,
        request: QueryClientStatesRequest,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        crate::time!("populate_clients");
        crate::telemetry!(query, self.id(), "populate_clients");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.chain.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let mut request = tonic::Request::new(request.into());
        let height_param = AsciiMetadataValue::try_from(*query_height)?;

        request
            .metadata_mut()
            .insert("x-cosmos-block-height", height_param);

        let response = self
            .block_on(client.client_states(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let clients = response
            .client_states
            .into_iter()
            .filter_map(|cs| IdentifiedAnyClientState::try_from(cs).ok());

        for c in clients {
            snapshot
                .data
                .client_states
                .entry(c.client_id.clone())
                .or_insert(c);
        }

        Ok(())
    }

    #[tracing::instrument(skip_all)]
    fn populate_consensus_states(
        &self,
        query_height: &QueryHeight,
        request: QueryConsensusStatesRequest,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        crate::time!("populate_consensus_states");
        crate::telemetry!(query, self.id(), "populate_consensus_states");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::client::v1::query_client::QueryClient::connect(
                    self.chain.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let client_id = request.client_id.clone();

        let mut request = tonic::Request::new(request.into());
        let height_param = AsciiMetadataValue::try_from(*query_height)?;

        request
            .metadata_mut()
            .insert("x-cosmos-block-height", height_param);

        let response = self
            .block_on(client.consensus_states(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let consensus_states = response
            .consensus_states
            .into_iter()
            .filter_map(|cs| AnyConsensusStateWithHeight::try_from(cs).ok());

        let entry = snapshot.data.consensus_states.entry(client_id).or_default();

        entry.extend(consensus_states);
        entry.sort_by(|a, b| b.height.cmp(&a.height));
        entry.dedup_by_key(|cs| cs.height);

        Ok(())
    }

    #[tracing::instrument(skip_all)]
    fn populate_connections(
        &self,
        query_height: &QueryHeight,
        request: QueryConnectionsRequest,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        crate::time!("populate_connections");
        crate::telemetry!(query, self.id(), "populate_connections");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::connection::v1::query_client::QueryClient::connect(
                    self.chain.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let mut request = tonic::Request::new(request.into());
        let height_param = AsciiMetadataValue::try_from(*query_height)?;

        request
            .metadata_mut()
            .insert("x-cosmos-block-height", height_param);

        let response = self
            .block_on(client.connections(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let response_height = response
            .height
            .unwrap()
            .try_into()
            .map_err(|_| Error::invalid_height_no_source())?;

        if let QueryHeight::Specific(height) = query_height {
            if height != &response_height {
                return Err(Error::invalid_height_no_source());
            }
        }

        let connections = response
            .connections
            .into_iter()
            .filter_map(|co| IdentifiedConnectionEnd::try_from(co).ok());

        for c in connections {
            snapshot
                .data
                .connections
                .entry(c.connection_id.clone())
                .or_insert(c);
        }

        snapshot.height = response_height.revision_height();

        Ok(())
    }

    #[tracing::instrument(skip_all)]
    fn populate_channels_and_pending_packets(
        &self,
        query_height: &QueryHeight,
        request: QueryChannelsRequest,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        crate::time!("populate_channels");
        crate::telemetry!(query, self.id(), "populate_channels");

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.chain.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let mut request = tonic::Request::new(request.into());
        let height_param = AsciiMetadataValue::try_from(*query_height)?;

        request
            .metadata_mut()
            .insert("x-cosmos-block-height", height_param);

        let response = self
            .block_on(client.channels(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let response_height = response
            .height
            .unwrap()
            .try_into()
            .map_err(|_| Error::invalid_height_no_source())?;

        if let QueryHeight::Specific(height) = query_height {
            if height != &response_height {
                return Err(Error::invalid_height_no_source());
            }
        }

        let channels: Vec<IdentifiedChannelEnd> = response
            .channels
            .into_iter()
            .filter_map(|ch| IdentifiedChannelEnd::try_from(ch).ok())
            .collect();

        for channel in channels.iter() {
            snapshot
                .data
                .channels
                .entry(Key(channel.port_channel_id()))
                .or_insert_with(|| channel.clone());

            self.populate_packets(query_height, channel, snapshot)?;
        }

        Ok(())
    }

    #[tracing::instrument(skip_all)]
    fn populate_packets(
        &self,
        query_height: &QueryHeight,
        c: &IdentifiedChannelEnd,
        snapshot: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        crate::time!("populate_packets");
        crate::telemetry!(query, self.id(), "populate_packets");

        let request = QueryPacketCommitmentsRequest {
            port_id: c.port_id.clone(),
            channel_id: c.channel_id.clone(),
            pagination: None,
        };

        let mut client = self
            .block_on(
                ibc_proto::ibc::core::channel::v1::query_client::QueryClient::connect(
                    self.chain.grpc_addr.clone(),
                ),
            )
            .map_err(Error::grpc_transport)?;

        let mut request = tonic::Request::new(request.into());
        let height_param = AsciiMetadataValue::try_from(*query_height)?;

        request
            .metadata_mut()
            .insert("x-cosmos-block-height", height_param);

        let response = self
            .block_on(client.packet_commitments(request))
            .map_err(Error::grpc_status)?
            .into_inner();

        let response_height = response
            .height
            .unwrap()
            .try_into()
            .map_err(|_| Error::invalid_height_no_source())?;

        if let QueryHeight::Specific(height) = query_height {
            if height != &response_height {
                return Err(Error::invalid_height_no_source());
            }
        }

        let mut sequences: Vec<Sequence> = response
            .commitments
            .into_iter()
            .map(|v| v.sequence.into())
            .collect();

        if sequences.is_empty() {
            return Ok(());
        }
        sequences.sort_unstable();

        let mut query = QueryPacketEventDataRequest {
            event_id: WithBlockDataType::SendPacket,
            source_channel_id: c.channel_id.clone(),
            source_port_id: c.port_id.clone(),
            destination_channel_id: c.channel_end.remote.channel_id.as_ref().unwrap().clone(),
            destination_port_id: c.channel_end.remote.port_id.clone(),
            sequences,
            height: Qualified::Equal(*query_height),
        };

        let results = self.block_on(query_packets_from_tendermint(
            &self.pool,
            self.id(),
            &mut query,
        ))?;

        for ev in results {
            let send_packet = downcast!(ev.event.clone() => IbcEvent::SendPacket)
                .ok_or_else(|| PsqlError::unexpected_event(ev.event))?;

            let packet_id = PacketId {
                channel_id: c.channel_id.clone(),
                port_id: c.port_id.clone(),
                sequence: send_packet.packet.sequence,
            };

            snapshot
                .data
                .pending_sent_packets
                .entry(packet_id)
                .or_insert_with(|| send_packet.packet);
        }

        Ok(())
    }

    #[tracing::instrument(skip(self))]
    fn compute_ibc_snapshot(&self, query_height: &Height) -> Result<IbcSnapshot, Error> {
        let mut result = IbcSnapshot {
            height: query_height.revision_height(),
            data: IbcData {
                app_status: self.chain_status_on_start(query_height).unwrap(),
                connections: HashMap::new(),
                channels: HashMap::new(),
                client_states: HashMap::new(),
                consensus_states: HashMap::new(),
                pending_sent_packets: HashMap::new(),
            },
        };

        self.populate_clients_and_consensus_states(
            &QueryHeight::Specific(*query_height),
            &mut result,
        )?;

        self.populate_connections(
            &QueryHeight::Specific(*query_height),
            QueryConnectionsRequest { pagination: None },
            &mut result,
        )?;

        self.populate_channels_and_pending_packets(
            &QueryHeight::Specific(*query_height),
            QueryChannelsRequest { pagination: None },
            &mut result,
        )?;

        Ok(result)
    }

    #[tracing::instrument(skip_all)]
    fn update_with_events(&mut self, batch: EventBatch) -> Result<(), Error> {
        let previous_height = batch.height.decrement().unwrap();

        // Get the snapshot at the previous height, which will
        // be updated by the events received at the current height.
        let mut snapshot = if !self.is_synced() {
            warn!("database is not synced, computing IBC snapshot");

            // Compute the snapshot for the previous height...
            let snapshot = self.compute_ibc_snapshot(&previous_height)?;

            // ...and store it
            self.rt
                .block_on(self.snapshot_store.update_snapshot(&snapshot))?;

            self.sync_state = PsqlSyncStatus::Synced;

            snapshot
        } else {
            let snapshot = self
                .snapshot_store
                .fetch_snapshot(QueryHeight::Specific(previous_height));

            self.rt.block_on(snapshot).map(Cow::into_owned)?
        };

        // Override with the current height
        snapshot.height = batch.height.revision_height();

        for event in batch.events {
            // Best effort to maintain the IBC snapshot based on events
            self.update_with_event(event, &mut snapshot);
        }

        // Insert the new snapshot for the current height
        self.rt
            .block_on(self.snapshot_store.update_snapshot(&snapshot))
    }

    fn try_update_with_create_client(
        &mut self,
        event: CreateClient,
        result: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        trace!("try_update_with_create_client {:?}", event);

        let client_state = self
            .chain
            .query_client_state(
                QueryClientStateRequest {
                    client_id: event.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(client_state, _proof)| {
                IdentifiedAnyClientState::new(event.client_id().clone(), client_state)
            })?;

        let consensus_states = self
            .chain
            .query_consensus_states(QueryConsensusStatesRequest {
                client_id: event.client_id().clone(),
                pagination: None,
            })?;

        debug!(
            "psql chain {} - adding client {} due to event {}",
            self.chain.id(),
            client_state.client_id,
            event
        );

        result
            .data
            .client_states
            .insert(event.client_id().clone(), client_state);

        result
            .data
            .consensus_states
            .insert(event.client_id().clone(), consensus_states);

        Ok(())
    }

    fn try_update_with_update_client(
        &mut self,
        event: UpdateClient,
        result: &mut IbcSnapshot,
    ) -> Result<(), Error> {
        trace!("try_update_with_update_client {:?}", event);

        // TODO - we should have everything in the UpdateClient event to build the consensus state
        // Client state should also be already present in the snapshots. Maybe do the gRPC query only
        // if somehow CreateClient was missed and therefore cannot be found in the snapshot.

        let client_state = self
            .chain
            .query_client_state(
                QueryClientStateRequest {
                    client_id: event.client_id().clone(),
                    height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map(|(client_state, _proof)| {
                IdentifiedAnyClientState::new(event.client_id().clone(), client_state)
            })?;

        let consensus_state = self
            .chain
            .query_consensus_state(
                QueryConsensusStateRequest {
                    client_id: event.client_id().clone(),
                    query_height: QueryHeight::Latest,
                    consensus_height: event.consensus_height(),
                },
                IncludeProof::No,
            )
            .map(|(consensus_state, _proof)| {
                AnyConsensusStateWithHeight::new(event.consensus_height(), consensus_state)
            })?;

        debug!(
            "psql chain {} - updating client {} due to event {}",
            self.chain.id(),
            client_state.client_id,
            event
        );

        result
            .data
            .client_states
            .insert(event.client_id().clone(), client_state);

        let entry = result
            .data
            .consensus_states
            .entry(event.client_id().clone())
            .or_insert_with(Vec::new);

        entry.push(consensus_state);
        entry.sort_by(|a, b| b.height.cmp(&a.height));
        entry.dedup_by_key(|cs| cs.height);

        Ok(())
    }

    fn try_update_with_client_event(&mut self, event: IbcEvent, result: &mut IbcSnapshot) {
        let _ = match event {
            IbcEvent::CreateClient(ev) => self.try_update_with_create_client(ev, result),
            IbcEvent::UpdateClient(ev) => self.try_update_with_update_client(ev, result),
            _ => Ok(()),
        };
    }

    #[tracing::instrument(skip(self))]
    fn maybe_chain_connection(
        &self,
        connection_id: &ConnectionId,
    ) -> Option<IdentifiedConnectionEnd> {
        let connection = self.chain.query_connection(
            QueryConnectionRequest {
                connection_id: connection_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        );
        match connection {
            Ok((connection_end, _p)) => Some(IdentifiedConnectionEnd::new(
                connection_id.clone(),
                connection_end,
            )),
            Err(e) => None,
        }
    }

    fn try_update_with_connection_event(&mut self, event: IbcEvent, result: &mut IbcSnapshot) {
        trace!("try_update_with_connection_event {:?}", event);

        // Connection events do not include the delay and version so a connection cannot be currently
        // fully constructed from an event. Because of this we need to query the chain directly for
        // Init and Try events.
        let connection = match event {
            IbcEvent::OpenInitConnection(ref ev) => {
                self.maybe_chain_connection(ev.connection_id().unwrap())
            }
            IbcEvent::OpenTryConnection(ref ev) => {
                self.maybe_chain_connection(ev.connection_id().unwrap())
            }
            _ => None,
        };

        match connection {
            None => {
                let new_partial_connection = events::connection_from_event(&event).unwrap();

                if let Some(ch) = result
                    .data
                    .connections
                    .get_mut(&new_partial_connection.connection_id)
                {
                    debug!(
                        "psql chain {} - changing connection {} from {} to {} due to event {}",
                        self.chain.id(),
                        ch.connection_id,
                        ch.connection_end.state.clone(),
                        new_partial_connection.connection_end.state,
                        event
                    );

                    ch.connection_end.state = new_partial_connection.connection_end.state;

                    // Update counterparty client and connection IDs only, don't overwrite the prefix.

                    ch.connection_end.counterparty.client_id = new_partial_connection
                        .connection_end
                        .counterparty()
                        .client_id
                        .clone();

                    ch.connection_end.counterparty.connection_id = new_partial_connection
                        .connection_end
                        .counterparty()
                        .connection_id
                        .clone();
                }
            }
            Some(connection) => {
                debug!(
                    "psql chain {} - changing connection {} from UNINITIALIZED to {} due to event {}",
                    self.chain.id(),
                    connection.connection_id,
                    connection.connection_end.state.clone(),
                    event
                );
                result
                    .data
                    .connections
                    .insert(connection.connection_id.clone(), connection);
            }
        }
    }

    fn maybe_chain_channel(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Option<IdentifiedChannelEnd> {
        let channel = self.chain.query_channel(
            QueryChannelRequest {
                port_id: port_id.clone(),
                channel_id: channel_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        );
        match channel {
            Ok((channel_end, _p)) => Some(IdentifiedChannelEnd {
                port_id: port_id.clone(),
                channel_id: channel_id.clone(),
                channel_end,
            }),
            Err(_e) => None,
        }
    }

    fn try_update_with_channel_event(&mut self, event: IbcEvent, result: &mut IbcSnapshot) {
        trace!("try_update_with_channel_event {:?}", event);

        // Channel events do not include the ordering and version so a channel cannot be currently
        // fully constructed from an event. Because of this we need to query the chain directly for
        // Init and Try events.
        let channel = match event {
            IbcEvent::OpenInitChannel(ref ev) => {
                self.maybe_chain_channel(&ev.port_id, ev.channel_id.as_ref().unwrap())
            }
            IbcEvent::OpenTryChannel(ref ev) => {
                self.maybe_chain_channel(&ev.port_id, ev.channel_id.as_ref().unwrap())
            }
            _ => None,
        };

        match channel {
            None => {
                let new_partial_channel = events::channel_from_event(&event).unwrap();

                if let Some(ch) = result
                    .data
                    .channels
                    .get_mut(&Key(new_partial_channel.port_channel_id()))
                {
                    debug!(
                        "psql chain {} - changing channel {} from {} to {} due to event {}",
                        self.chain.id(),
                        ch.channel_id,
                        ch.channel_end.state.clone(),
                        new_partial_channel.channel_end.state,
                        event
                    );

                    ch.channel_end.state = new_partial_channel.channel_end.state;
                    ch.channel_end.remote = new_partial_channel.channel_end.remote;
                }
            }
            Some(channel) => {
                debug!(
                    "psql chain {} - changing channel {} from UNINITIALIZED to {} due to event {}",
                    self.chain.id(),
                    channel.channel_id,
                    channel.channel_end.state.clone(),
                    event
                );

                result
                    .data
                    .channels
                    .insert(Key(channel.port_channel_id()), channel);
            }
        }
    }

    fn try_update_with_packet_event(&mut self, event: IbcEvent, snapshot: &mut IbcSnapshot) {
        trace!("try_update_with_packet_event {:?}", event);

        match event {
            IbcEvent::SendPacket(sp) => {
                let packet_id = PacketId {
                    port_id: sp.src_port_id().clone(),
                    channel_id: sp.src_channel_id().clone(),
                    sequence: sp.packet.sequence,
                };

                debug!(
                    "psql chain {} - inserting pending sent packet '{}' due to event SendPacket({})",
                    self.chain.id(),
                    packet_id,
                    sp
                );

                snapshot
                    .data
                    .pending_sent_packets
                    .insert(packet_id, sp.packet);
            }
            IbcEvent::AcknowledgePacket(ap) => {
                let packet_id = PacketId {
                    port_id: ap.src_port_id().clone(),
                    channel_id: ap.src_channel_id().clone(),
                    sequence: ap.packet.sequence,
                };

                let removed = snapshot.data.pending_sent_packets.remove(&packet_id);

                match removed {
                    Some(_) => debug!(
                        "removed pending packet '{}' due to event AcknowledgePacket({})",
                        packet_id, ap
                    ),
                    None => debug!(
                        "no pending send packet found by ack event for '{}' due to event AcknowledgePacket({})",
                        packet_id, ap
                    ),
                }
            }
            _ => {}
        }
    }

    // Get the chain status on start. The block at height needs to be retrieved via RPC as
    // there is no available event for height.
    fn chain_status_on_start(&self, height: &Height) -> Option<ChainStatus> {
        crate::time!("chain_status_on_start");
        crate::telemetry!(query, self.id(), "chain_status_on_start");
        let tm_height = block::Height::try_from(height.revision_height()).unwrap();

        self.block_on(self.chain.rpc_client.blockchain(tm_height, tm_height))
            .map_or_else(
                |_| None,
                |response| {
                    response.block_metas.first().map(|b| ChainStatus {
                        height: *height,
                        timestamp: b.header.time.into(),
                    })
                },
            )
    }

    // Currently same as chain_status_on_start since the block is not propagated from the monitor
    // to the supervisor and then here in the runtime.
    // TODO - include the block in the NewBlock event and use here.
    fn chain_status_from_block_event(&self, block_event: &NewBlock) -> Option<ChainStatus> {
        crate::time!("chain_status_from_event");
        crate::telemetry!(query, self.id(), "chain_status_from_event");

        let tm_height = block::Height::try_from(block_event.height.revision_height()).unwrap();
        self.block_on(self.chain.rpc_client.blockchain(tm_height, tm_height))
            .map_or_else(
                |_| None,
                |response| {
                    response.block_metas.first().map(|b| ChainStatus {
                        height: block_event.height,
                        timestamp: b.header.time.into(),
                    })
                },
            )
    }

    fn update_with_event(&mut self, event: IbcEventWithHeight, snapshot: &mut IbcSnapshot) {
        let event = event.event;

        // TODO - There should be a NewBlock event in the caller's batch.
        // If not we need to figure out that the app_status has not been updated in this snapshot
        // and do an explicit block query.
        if let IbcEvent::NewBlock(b) = event {
            if let Some(status) = self.chain_status_from_block_event(&b) {
                snapshot.data.app_status = status;
            }
        }

        if events::is_packet_event(&event) {
            self.try_update_with_packet_event(event, snapshot);
        } else if events::is_client_event(&event) {
            self.try_update_with_client_event(event, snapshot);
        } else if events::is_connection_event(&event) {
            self.try_update_with_connection_event(event, snapshot);
        } else if events::is_channel_event(&event) {
            self.try_update_with_channel_event(event, snapshot);
        }
    }
}

impl ChainEndpoint for PsqlChain {
    type LightBlock = <CosmosSdkChain as ChainEndpoint>::LightBlock;

    type Header = <CosmosSdkChain as ChainEndpoint>::Header;

    type ConsensusState = <CosmosSdkChain as ChainEndpoint>::ConsensusState;

    type ClientState = <CosmosSdkChain as ChainEndpoint>::ClientState;

    fn bootstrap(config: ChainConfig, rt: Arc<tokio::runtime::Runtime>) -> Result<Self, Error> {
        info!("bootstrapping");

        let psql_conn = config
            .psql_conn
            .as_deref()
            .ok_or_else(|| PsqlError::missing_connection_config(config.id.clone()))?;

        let pool = rt
            .block_on(PgPoolOptions::new().max_connections(5).connect(psql_conn))
            .map_err(Error::sqlx)?;

        let snapshot_store: Box<dyn SnapshotStore> =
            match config.snapshot_store.unwrap_or(SnapshotStoreType::Psql) {
                SnapshotStoreType::Psql => Box::new(PsqlSnapshotStore::new(pool.clone())),
                SnapshotStoreType::Memory => Box::new(MemorySnapshotStore::new()),
            };

        info!("instantiating chain");

        let chain = CosmosSdkChain::bootstrap(config, rt.clone())?;

        Ok(Self {
            chain,
            pool,
            snapshot_store,
            rt,
            sync_state: PsqlSyncStatus::Unknown,
        })
    }

    fn subscribe(&mut self) -> Result<Subscription, Error> {
        self.chain.subscribe()
    }

    fn id(&self) -> &ChainId {
        self.chain.id()
    }

    fn shutdown(self) -> Result<(), Error> {
        self.chain.shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        // TODO(ibcnode): Check database connection

        self.chain.health_check()
    }

    fn keybase(&self) -> &KeyRing {
        self.chain.keybase()
    }

    fn keybase_mut(&mut self) -> &mut KeyRing {
        self.chain.keybase_mut()
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let runtime = self.rt.clone();
        runtime.block_on(self.do_send_messages_and_wait_commit(tracked_msgs))
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tx_sync::Response>, Error> {
        self.chain.send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        self.chain.get_signer()
    }

    fn config(&self) -> &ChainConfig {
        ChainEndpoint::config(&self.chain)
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        self.chain.get_key()
    }

    fn add_key(&mut self, key_name: &str, key: KeyEntry) -> Result<(), Error> {
        self.chain.add_key(key_name, key)
    }

    fn ibc_version(&self) -> Result<Option<Version>, Error> {
        self.chain.ibc_version()
    }

    fn ibc_snapshot(&self) -> Result<Option<IbcSnapshot>, Error> {
        let snapshot = self.block_on(self.snapshot_store.fetch_snapshot(QueryHeight::Latest))?;
        Ok(Some(snapshot.into_owned()))
    }

    fn query_balance(&self, key_name: Option<&str>, denom: Option<&str>) -> Result<Balance, Error> {
        self.chain.query_balance(key_name, denom)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.chain.query_commitment_prefix()
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        if self.is_synced() {
            crate::time!("query_application_status_psql");
            crate::telemetry!(query, self.id(), "query_application_status_psql");
            self.block_on(self.snapshot_store.query_application_status())
        } else {
            self.chain.query_application_status()
        }
    }

    fn handle_ibc_event_batch(&mut self, batch: EventBatch) -> Result<(), Error> {
        crate::time!("handle_ibc_event_batch");
        crate::telemetry!(query, self.id(), "handle_ibc_event_batch");

        self.update_with_events(batch)
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        if self.is_synced() {
            crate::time!("query_clients_psql");
            crate::telemetry!(query, self.id(), "query_clients_psql");

            self.block_on(self.snapshot_store.query_clients(QueryHeight::Latest))
        } else {
            self.chain.query_clients(request)
        }
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        if self.is_synced() && include_proof.is_no() {
            crate::time!("query_client_state_psql");
            crate::telemetry!(query, self.id(), "query_client_state_psql");

            let client_state = self.block_on(self.snapshot_store.query_client_state(request))?;
            Ok((client_state, None))
        } else {
            self.chain.query_client_state(request, include_proof)
        }
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        if self.is_synced() {
            crate::time!("query_consensus_states_psql");
            crate::telemetry!(query, self.id(), "query_consensus_states_psql");

            self.block_on(
                self.snapshot_store
                    .query_consensus_states(QueryHeight::Latest, request),
            )
        } else {
            self.chain.query_consensus_states(request)
        }
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        if self.is_synced() && include_proof.is_no() {
            crate::time!("query_consensus_state_psql");
            crate::telemetry!(query, self.id(), "query_consensus_state_psql");

            let states = self.block_on(self.snapshot_store.query_consensus_state(request))?;

            Ok((states, None))
        } else {
            self.chain.query_consensus_state(request, include_proof)
        }
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        self.chain.query_upgraded_client_state(request)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        self.chain.query_upgraded_consensus_state(request)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        if self.is_synced() {
            crate::time!("query_connections_psql");
            crate::telemetry!(query, self.id(), "query_connections_psql");

            self.block_on(self.snapshot_store.query_connections(QueryHeight::Latest))
        } else {
            warn!(
                "chain psql dbs not synchronized on {}, falling back to gRPC query_connections",
                self.id()
            );

            self.chain.query_connections(request)
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        if self.is_synced() {
            crate::time!("query_client_connections_psql");
            crate::telemetry!(query, self.id(), "query_client_connections_psql");

            self.block_on(
                self.snapshot_store
                    .query_client_connections(QueryHeight::Latest, &request.client_id),
            )
        } else {
            warn!(
                "chain psql dbs not synchronized on {}, falling back to gRPC query_client_connections",
                self.id()
            );

            self.chain.query_client_connections(request)
        }
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        if include_proof.is_yes() {
            return self.chain.query_connection(request, include_proof);
        }

        if self.is_synced() {
            crate::time!("query_connection_psql");
            crate::telemetry!(query, self.id(), "query_connection_psql");

            let connection_end = self
                .block_on(
                    self.snapshot_store
                        .query_connection(request.height, &request.connection_id),
                )?
                .ok_or_else(|| PsqlError::connection_not_found(request.connection_id.clone()))?
                .connection_end;

            Ok((connection_end, None))
        } else {
            warn!(
                "chain psql dbs not synchronized on {}, falling back to gRPC query_connection for {}",
                self.chain.id(), request.connection_id
            );

            self.chain.query_connection(request, include_proof)
        }
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        if self.is_synced() {
            crate::time!("query_channels_psql");
            crate::telemetry!(query, self.id(), "query_channels_psql");

            self.block_on(
                self.snapshot_store
                    .query_connection_channels(QueryHeight::Latest, &request.connection_id),
            )
        } else {
            warn!(
                "chain psql dbs not synchronized on {}, falling back to gRPC query_connection_channels",
                self.chain.id()
            );

            self.chain.query_connection_channels(request)
        }
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        if self.is_synced() {
            crate::time!("query_channels_psql");
            crate::telemetry!(query, self.id(), "query_channels_psql");

            self.block_on(self.snapshot_store.query_channels(QueryHeight::Latest))
        } else {
            warn!(
                "chain psql dbs not synchronized on {}, falling back to gRPC query_channels",
                self.chain.id()
            );

            self.chain.query_channels(request)
        }
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        match include_proof {
            IncludeProof::Yes => self.chain.query_channel(request, include_proof),
            IncludeProof::No => {
                if self.is_synced() {
                    crate::time!("query_channel_psql");
                    crate::telemetry!(query, self.id(), "query_channel_psql");

                    let port_channel_id =
                        PortChannelId::new(request.channel_id.clone(), request.port_id.clone());

                    let channel_end = self
                        .block_on(
                            self.snapshot_store
                                .query_channel(request.height, &port_channel_id),
                        )?
                        .ok_or_else(|| PsqlError::channel_not_found(request.channel_id.clone()))?
                        .channel_end;

                    Ok((channel_end, None))
                } else {
                    warn!("chain psql dbs not synchronized on {}, falling back to gRPC query_channel for {}/{}",
                    self.chain.id(), request.port_id, request.channel_id);
                    self.chain.query_channel(request, include_proof)
                }
            }
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        self.chain.query_channel_client_state(request)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.chain.query_packet_commitments(request)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.chain.query_unreceived_packets(request)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        self.chain.query_packet_acknowledgements(request)
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        self.chain.query_unreceived_acknowledgements(request)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        self.chain
            .query_next_sequence_receive(request, include_proof)
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        if self.is_synced() {
            crate::time!("query_txs_snapshots_psql");
            crate::telemetry!(query, self.id(), "query_txs_snapshots_psql");
            self.block_on(query_txs_from_ibc_snapshots(
                &self.pool,
                self.id(),
                &request,
            ))
        } else {
            crate::time!("query_txs_tendermint_psql");
            crate::telemetry!(query, self.id(), "query_txs_tendermint_psql");
            self.block_on(query_txs_from_tendermint(&self.pool, self.id(), &request))
        }
    }

    fn query_packet_events(
        &self,
        mut request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        if self.is_synced() {
            crate::time!("query_packet_events_psql");
            crate::telemetry!(query, self.id(), "query_packet_events_psql");
            self.block_on(query_packets_from_ibc_snapshots(
                &self.pool,
                self.snapshot_store.as_ref(),
                self.id(),
                &mut request,
            ))
        } else {
            crate::time!("query_packets_from_tendermint");
            crate::telemetry!(query, self.id(), "query_packets_from_tendermint");
            self.block_on(query_packets_from_tendermint(
                &self.pool,
                self.id(),
                &mut request,
            ))
        }
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<Self::ConsensusState, Error> {
        self.chain.query_host_consensus_state(request)
    }

    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<Self::ClientState, Error> {
        self.chain.build_client_state(height, settings)
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        self.chain.build_consensus_state(light_block)
    }

    fn build_header(
        &mut self,
        trusted_height: Height,
        target_height: Height,
        client_state: &AnyClientState,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        self.chain
            .build_header(trusted_height, target_height, client_state)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain.query_packet_commitment(request, include_proof)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain.query_packet_receipt(request, include_proof)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        self.chain
            .query_packet_acknowledgement(request, include_proof)
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        self.chain.query_denom_trace(hash)
    }

    fn verify_header(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Self::LightBlock, Error> {
        self.chain.verify_header(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &mut self,
        update: &UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.chain.check_misbehaviour(update, client_state)
    }

    fn query_all_balances(&self, key_name: Option<&str>) -> Result<Vec<Balance>, Error> {
        self.chain.query_all_balances(key_name)
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_payee: &Signer,
    ) -> Result<(), Error> {
        self.chain
            .maybe_register_counterparty_payee(channel_id, port_id, counterparty_payee)
    }
}
