#![allow(unused_variables, dead_code)]

use alloc::sync::Arc;
use core::future::Future;
use std::collections::HashMap;

use semver::Version;
use sqlx::postgres::{PgPool, PgPoolOptions};
use tendermint::block;
use tendermint_rpc::endpoint::broadcast::tx_sync;
use tendermint_rpc::Client;
use tonic::metadata::AsciiMetadataValue;
use tracing::{debug, info, span, trace, warn, Level};

use ibc::core::ics02_client::events::NewBlock;
use ibc::{
    core::{
        ics02_client::{
            client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight},
            client_state::{AnyClientState, IdentifiedAnyClientState},
            events::UpdateClient,
            misbehaviour::MisbehaviourEvidence,
        },
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::Sequence,
        },
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId},
    },
    downcast,
    events::{IbcEvent, WithBlockDataType},
    Height,
};

use crate::chain::cosmos::CosmosSdkChain;
use crate::chain::psql_cosmos::batch::send_batched_messages_and_wait_commit;
use crate::chain::psql_cosmos::query::{
    query_application_status, query_blocks, query_channel, query_channels, query_connection,
    query_connections, query_ibc_data, query_txs_from_ibc_snapshots, query_txs_from_tendermint,
};
use crate::chain::psql_cosmos::update::{update_dbs, PacketId};
use crate::chain::psql_cosmos::update::{IbcData, IbcSnapshot};
use crate::denom::DenomTrace;
use crate::event::monitor::EventBatch;
use crate::{
    account::Balance,
    chain::{
        client::ClientSettings,
        endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
        requests::*,
        tracking::TrackedMsgs,
    },
    config::ChainConfig,
    error::Error,
    event::monitor::{EventReceiver, TxMonitorCmd},
    keyring::{KeyEntry, KeyRing},
    light_client::{tendermint::LightClient as TmLightClient, LightClient, Verified},
};

use super::cosmos::query::account::get_or_fetch_account;
use super::requests::{QueryBlockRequest, QueryTxRequest};

pub mod batch;
mod events;
pub mod query;
pub mod update;
pub mod wait;

flex_error::define_error! {
    PsqlError {
        MissingConnectionConfig
            { chain_id: ChainId }
            |e| { format_args!("missing `psql_conn` config for chain '{}'", e.chain_id) }
    }
}

pub struct PsqlChain {
    chain: CosmosSdkChain,
    pool: PgPool,
    rt: Arc<tokio::runtime::Runtime>,
    starting: bool,
}

impl PsqlChain {
    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        crate::time!("block_on");
        self.rt.block_on(f)
    }

    async fn do_send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEvent>, Error> {
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

        let connections: Vec<IdentifiedConnectionEnd> = response
            .connections
            .into_iter()
            .filter_map(|co| IdentifiedConnectionEnd::try_from(co).ok())
            .collect();

        for c in connections.iter() {
            snapshot
                .json_data
                .connections
                .entry(c.connection_id.clone())
                .or_insert_with(|| c.clone());
        }
        snapshot.height = response_height.revision_height();
        Ok(())
    }

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

        for c in channels.iter() {
            snapshot
                .json_data
                .channels
                .entry(c.channel_id.clone())
                .or_insert_with(|| c.clone());
            self.populate_packets(query_height, c, snapshot)?;
        }

        Ok(())
    }

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

        let results = self.block_on(query_txs_from_tendermint(
            &self.pool,
            self.id(),
            &QueryTxRequest::Packet(QueryPacketEventDataRequest {
                event_id: WithBlockDataType::SendPacket,
                source_channel_id: c.channel_id.clone(),
                source_port_id: c.port_id.clone(),
                destination_channel_id: c.channel_end.remote.channel_id.as_ref().unwrap().clone(),
                destination_port_id: c.channel_end.remote.port_id.clone(),
                sequences,
                height: *query_height,
            }),
        ))?;

        for ev in results.iter() {
            let send_packet = downcast!(ev.clone() => IbcEvent::SendPacket)
                .ok_or_else(Error::invalid_height_no_source)?;
            let packet_id = PacketId {
                channel_id: c.channel_id.clone(),
                port_id: c.port_id.clone(),
                sequence: send_packet.packet.sequence,
            };

            snapshot
                .json_data
                .pending_sent_packets
                .entry(PacketId {
                    channel_id: c.channel_id.clone(),
                    port_id: c.port_id.clone(),
                    sequence: send_packet.packet.sequence,
                })
                .or_insert_with(|| send_packet.packet);
        }

        Ok(())
    }

    fn ibc_snapshot(&self, query_height: &Height) -> Result<IbcSnapshot, Error> {
        let mut result = IbcSnapshot {
            height: query_height.revision_height(),
            json_data: IbcData {
                app_status: self.chain_status_on_start(query_height).unwrap(),
                connections: HashMap::new(),
                channels: HashMap::new(),
                pending_sent_packets: HashMap::new(),
            },
        };

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

    fn update_with_events(&mut self, batch: EventBatch) -> Result<(), Error> {
        let previous_height = batch.height.decrement().unwrap();
        if self.starting {
            let snapshot = self.ibc_snapshot(&previous_height)?;
            self.block_on(update_dbs(&self.pool.clone(), &snapshot))?;
            self.starting = false;
        }

        let mut work_copy = self.block_on(query_ibc_data(
            &self.pool,
            &QueryHeight::Specific(previous_height),
        ))?;
        work_copy.height = batch.height.revision_height();

        for event in batch.events.iter() {
            // best effort to maintain the IBC snapshot based on events
            self.update_with_event(event, &mut work_copy);
        }

        self.block_on(update_dbs(&self.pool, &work_copy))
    }

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
            Ok((connection_end, _p)) => Some(IdentifiedConnectionEnd {
                connection_id: connection_id.clone(),
                connection_end,
            }),
            Err(e) => None,
        }
    }

    fn try_update_with_connection_event(&mut self, event: &IbcEvent, result: &mut IbcSnapshot) {
        // Connection events do not include the delay and version so a connection cannot be currently
        // fully constructed from an event. Because of this we need to query the chain directly for
        // Init and Try events.
        let connection = match event {
            IbcEvent::OpenInitConnection(ev) => {
                self.maybe_chain_connection(&ev.connection_id().cloned().unwrap())
            }
            IbcEvent::OpenTryConnection(ev) => {
                self.maybe_chain_connection(&ev.connection_id().cloned().unwrap())
            }
            _ => None,
        };

        match connection {
            None => {
                let new_partial_connection = events::connection_from_event(event).unwrap();
                if let Some(ch) = result
                    .json_data
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
                    ch.connection_end.counterparty.client_id = new_partial_connection.connection_end.counterparty().client_id.clone();
                    ch.connection_end.counterparty.connection_id = new_partial_connection.connection_end.counterparty().connection_id.clone();
                }
            }
            Some(connection) => {
                debug!(
                    "psql chain {} - changing connection {} from uninit to {} due to event {}",
                    self.chain.id(),
                    connection.connection_id,
                    connection.connection_end.state.clone(),
                    event
                );
                result
                    .json_data
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

    fn try_update_with_channel_event(&mut self, event: &IbcEvent, result: &mut IbcSnapshot) {
        // Channel events do not include the ordering and version so a channel cannot be currently
        // fully constructed from an event. Because of this we need to query the chain directly for
        // Init and Try events.
        let channel = match event {
            IbcEvent::OpenInitChannel(ev) => {
                self.maybe_chain_channel(&ev.port_id, &ev.channel_id.clone().unwrap())
            }
            IbcEvent::OpenTryChannel(ev) => {
                self.maybe_chain_channel(&ev.port_id, &ev.channel_id.clone().unwrap())
            }
            _ => None,
        };

        match channel {
            None => {
                let new_partial_channel = events::channel_from_event(event).unwrap();
                if let Some(ch) = result
                    .json_data
                    .channels
                    .get_mut(&new_partial_channel.channel_id)
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
                    "psql chain {} - changing channel {} from uninit to {} due to event {}",
                    self.chain.id(),
                    channel.channel_id,
                    channel.channel_end.state.clone(),
                    event
                );
                result
                    .json_data
                    .channels
                    .insert(channel.channel_id.clone(), channel);
            }
        }
    }

    fn try_update_with_packet_event(&mut self, event: &IbcEvent, snapshot: &mut IbcSnapshot) {
        match event {
            IbcEvent::SendPacket(sp) => {
                let key = PacketId {
                    port_id: sp.src_port_id().clone(),
                    channel_id: sp.src_channel_id().clone(),
                    sequence: sp.packet.sequence,
                };
                snapshot
                    .json_data
                    .pending_sent_packets
                    .entry(key)
                    .and_modify(|e| *e = sp.packet.clone())
                    .or_insert_with(|| sp.packet.clone());
            }
            IbcEvent::AcknowledgePacket(ap) => {
                let key = PacketId {
                    port_id: ap.src_port_id().clone(),
                    channel_id: ap.src_channel_id().clone(),
                    sequence: ap.packet.sequence,
                };
                let removed = snapshot.json_data.pending_sent_packets.remove(&key);
                match removed {
                    Some(p) => trace!("removed pending packet {:?}", key),
                    None => debug!("no pending send packet found by ack event for {:?}", key),
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

    fn update_with_event(&mut self, event: &IbcEvent, snapshot: &mut IbcSnapshot) {
        // TODO - There should be a NewBlock event in the caller's batch.
        // If not we need to figure out that the app_status has not been updated in this snapshot
        // and do an explicit block query.
        if let IbcEvent::NewBlock(b) = event {
            if let Some(status) = self.chain_status_from_block_event(b) {
                snapshot.json_data.app_status = status
            }
        }

        if events::is_connection_event(event) {
            dbg!(&event);
            self.try_update_with_connection_event(event, snapshot);
        }

        if events::is_channel_event(event) {
            self.try_update_with_channel_event(event, snapshot);
        }
        if events::is_packet_event(event) {
            self.try_update_with_packet_event(event, snapshot);
        }
    }
}

impl ChainEndpoint for PsqlChain {
    type LightBlock = <CosmosSdkChain as ChainEndpoint>::LightBlock;

    type Header = <CosmosSdkChain as ChainEndpoint>::Header;

    type ConsensusState = <CosmosSdkChain as ChainEndpoint>::ConsensusState;

    type ClientState = <CosmosSdkChain as ChainEndpoint>::ClientState;

    type LightClient = PsqlLightClient;

    fn bootstrap(config: ChainConfig, rt: Arc<tokio::runtime::Runtime>) -> Result<Self, Error> {
        info!("bootstrapping");

        let psql_conn = config
            .psql_conn
            .as_deref()
            .ok_or_else(|| PsqlError::missing_connection_config(config.id.clone()))?;

        let pool = rt
            .block_on(PgPoolOptions::new().max_connections(5).connect(psql_conn))
            .map_err(Error::sqlx)?;

        info!("instantiating chain");

        let chain = CosmosSdkChain::bootstrap(config, rt.clone())?;

        Ok(Self {
            chain,
            pool,
            rt,
            starting: true,
        })
    }

    fn init_light_client(&self) -> Result<Self::LightClient, Error> {
        self.chain.init_light_client().map(PsqlLightClient)
    }

    fn init_event_monitor(
        &self,
        rt: Arc<tokio::runtime::Runtime>,
    ) -> Result<(EventReceiver, TxMonitorCmd), Error> {
        self.chain.init_event_monitor(rt)
    }

    fn id(&self) -> &ChainId {
        // let _ = &self.pool;
        // let _ = &self.rt;
        self.chain.id()
    }

    fn shutdown(self) -> Result<(), Error> {
        self.chain.shutdown()
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        // TODO(romac): Check database connection

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
    ) -> Result<Vec<IbcEvent>, Error> {
        let runtime = self.rt.clone();
        runtime.block_on(self.do_send_messages_and_wait_commit(tracked_msgs))
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tx_sync::Response>, Error> {
        self.chain.send_messages_and_wait_check_tx(tracked_msgs)
    }

    fn get_signer(&mut self) -> Result<ibc::signer::Signer, Error> {
        self.chain.get_signer()
    }

    fn config(&self) -> ChainConfig {
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

    fn query_balance(&self, key_name: Option<String>) -> Result<Balance, Error> {
        self.chain.query_balance(key_name)
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        self.chain.query_commitment_prefix()
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        crate::time!("query_application_status_psql");
        crate::telemetry!(query, self.id(), "query_application_status_psql");
        self.block_on(query_application_status(&self.pool))
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
        self.chain.query_clients(request)
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        self.chain.query_client_state(request, include_proof)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<Vec<AnyConsensusStateWithHeight>, Error> {
        self.chain.query_consensus_states(request)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        self.chain.query_consensus_state(request, include_proof)
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
        match self.block_on(query_connections(&self.pool, &QueryHeight::Latest)) {
            Ok(connections) => {
                crate::telemetry!(query, self.id(), "query_connections_psql");
                Ok(connections)
            }
            Err(e) => {
                warn!(
                    "unable to query_connections via psql connection ({}), falling back to gRPC",
                    e
                );
                self.chain.query_connections(request)
            }
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        self.chain.query_client_connections(request)
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        match include_proof {
            IncludeProof::Yes => self.chain.query_connection(request, include_proof),
            IncludeProof::No => {
                match self.block_on(query_connection(
                    &self.pool,
                    &request.height,
                    &request.connection_id,
                )) {
                    Ok(Some(connection)) => {
                        crate::telemetry!(query, self.id(), "query_connections_psql");
                        Ok((connection.connection_end, None))
                    }
                    _ => {
                        warn!(
                            "unable to query_connection via psql connection, falling back to gRPC"
                        );
                        self.chain.query_connection(request, include_proof)
                    }
                }
            }
        }
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        self.chain.query_connection_channels(request)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        crate::time!("query_channels");
        match self.block_on(query_channels(&self.pool, &QueryHeight::Latest)) {
            Ok(channels) => {
                crate::telemetry!(query, self.id(), "query_channels_psql");
                Ok(channels)
            }
            Err(e) => {
                warn!(
                    "unable to query_channels via psql connection ({}), falling back to gRPC",
                    e
                );
                self.chain.query_channels(request)
            }
        }
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        crate::time!("query_channel_psql");

        match include_proof {
            IncludeProof::Yes => self.chain.query_channel(request, include_proof),
            IncludeProof::No => {
                match self.block_on(query_channel(
                    &self.pool,
                    &request.height,
                    &request.channel_id,
                )) {
                    Ok(Some(channel)) => {
                        crate::telemetry!(query, self.id(), "query_channel_psql");
                        Ok((channel.channel_end, None))
                    }
                    _ => {
                        warn!("unable to query_channel via psql connection, falling back to gRPC");
                        self.chain.query_channel(request, include_proof)
                    }
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

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEvent>, Error> {
        crate::time!("query_txs_psql");
        crate::telemetry!(query, self.id(), "query_txs");

        self.block_on(query_txs_from_ibc_snapshots(
            &self.pool,
            self.id(),
            &request,
        ))
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
    ) -> Result<(Vec<IbcEvent>, Vec<IbcEvent>), Error> {
        // Currently the psql tendermint DB does not distinguish between begin and end block events.
        // The SQL query in `query_blocks` returns all block events
        let all_block_events = self.block_on(query_blocks(&self.pool, self.id(), &request))?;
        Ok((all_block_events, vec![]))
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
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: &AnyClientState,
        light_client: &mut Self::LightClient,
    ) -> Result<(Self::Header, Vec<Self::Header>), Error> {
        self.chain.build_header(
            trusted_height,
            target_height,
            client_state,
            &mut light_client.0,
        )
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
}

pub struct PsqlLightClient(TmLightClient);

impl LightClient<PsqlChain> for PsqlLightClient {
    fn header_and_minimal_set(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<<PsqlChain as ChainEndpoint>::Header>, Error> {
        self.0.header_and_minimal_set(trusted, target, client_state)
    }

    fn verify(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: &AnyClientState,
    ) -> Result<Verified<<PsqlChain as ChainEndpoint>::LightBlock>, Error> {
        self.0.verify(trusted, target, client_state)
    }

    fn check_misbehaviour(
        &mut self,
        update: UpdateClient,
        client_state: &AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        self.0.check_misbehaviour(update, client_state)
    }

    fn fetch(&mut self, height: Height) -> Result<<PsqlChain as ChainEndpoint>::LightBlock, Error> {
        self.0.fetch(height)
    }
}
