#![allow(unused_variables, dead_code)]

use alloc::sync::Arc;
use core::future::Future;
use std::collections::HashMap;

use semver::Version;
use sqlx::postgres::{PgPool, PgPoolOptions};
use tendermint_rpc::endpoint::broadcast::tx_sync;
use tonic::metadata::AsciiMetadataValue;
use tracing::{debug, info, span, trace, warn, Level};

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
            channel::{ChannelEnd, Counterparty, IdentifiedChannelEnd, Order, State},
            packet::Sequence,
            Version as ChannelVersion,
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
    query_blocks, query_channel, query_channels, query_connections, query_ibc_data,
    query_txs_from_ibc_snapshots, query_txs_from_tendermint,
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
            // TODO AZ
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

    fn solve_query_height(&self, query_height: &QueryHeight) -> Result<Height, Error> {
        let solved_height = if let QueryHeight::Specific(height) = query_height {
            *height
        } else {
            self.chain.query_application_status()?.height
        };
        Ok(solved_height)
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

    fn ibc_snapshot(&self, query_height: &QueryHeight) -> Result<IbcSnapshot, Error> {
        let solved_query_height = self.solve_query_height(query_height)?;

        let mut result = IbcSnapshot {
            height: solved_query_height.revision_height(),
            json_data: IbcData {
                connections: HashMap::new(),
                channels: HashMap::new(),
                pending_sent_packets: HashMap::new(),
            },
        };

        self.populate_connections(
            &QueryHeight::Specific(solved_query_height),
            QueryConnectionsRequest { pagination: None },
            &mut result,
        )?;

        self.populate_channels_and_pending_packets(
            &QueryHeight::Specific(solved_query_height),
            QueryChannelsRequest { pagination: None },
            &mut result,
        )?;

        Ok(result)
    }

    fn update_with_events(&mut self, batch: EventBatch) -> Result<(), Error> {
        if self.starting {
            let snapshot =
                self.ibc_snapshot(&QueryHeight::Specific(batch.height.decrement().unwrap()))?;
            self.block_on(update_dbs(&self.pool.clone(), &snapshot))?;
            self.starting = false;
        }

        let height = batch.height.revision_height();
        let latest = self.block_on(query_ibc_data(&self.pool, height))?;
        let mut work_copy = latest.clone();
        work_copy.height = height;

        for event in batch.events.iter() {
            // best effort to maintain the IBC snapshot based on events
            self.update_with_event(event, &mut work_copy);
        }

        if work_copy.json_data != latest.json_data {
            self.block_on(update_dbs(&self.pool, &work_copy))
        } else {
            Ok(())
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
                let new_partial_channel = channel_from_event(event).unwrap();
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

    fn update_with_event(&mut self, event: &IbcEvent, snapshot: &mut IbcSnapshot) {
        if is_channel_event(event) {
            self.try_update_with_channel_event(event, snapshot);
        }
        if is_packet_event(event) {
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
        self.chain.query_application_status()
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
        let query_height = self
            .chain
            .query_application_status()?
            .height
            .revision_height();

        match self.block_on(query_connections(&self.pool, query_height)) {
            Ok(connections) => Ok(connections),
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
        self.chain.query_connection(request, include_proof)
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
        let query_height = self
            .chain
            .query_application_status()?
            .height
            .revision_height();
        match self.block_on(query_channels(&self.pool, query_height)) {
            Ok(channels) => Ok(channels),
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
        crate::telemetry!(query, self.id(), "query_channel_psql");
        match include_proof {
            IncludeProof::Yes => self.chain.query_channel(request, include_proof),
            IncludeProof::No => {
                let query_height = self.solve_query_height(&request.height)?.revision_height();

                match self.block_on(query_channel(
                    &self.pool,
                    query_height,
                    request.channel_id.clone(),
                )) {
                    Ok(Some(channel)) => Ok((channel.channel_end, None)),
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
        crate::time!("query_txs");
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

pub fn is_channel_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::OpenInitChannel(_)
            | &IbcEvent::OpenTryChannel(_)
            | &IbcEvent::OpenAckChannel(_)
            | &IbcEvent::OpenConfirmChannel(_)
    )
}

pub fn is_packet_event(event: &IbcEvent) -> bool {
    matches!(
        event,
        &IbcEvent::SendPacket(_)
            | &IbcEvent::WriteAcknowledgement(_)
            | &IbcEvent::AcknowledgePacket(_)
    )
}

macro_rules! event_to_channel {
    ($ev:expr, $state:expr) => {
        IdentifiedChannelEnd {
            port_id: $ev.port_id.clone(),
            channel_id: $ev.channel_id.clone().unwrap(),
            channel_end: ChannelEnd {
                state: $state,
                ordering: Order::None, // missing
                remote: Counterparty {
                    port_id: $ev.counterparty_port_id.clone(),
                    channel_id: $ev.counterparty_channel_id.clone(),
                },
                connection_hops: vec![$ev.connection_id.clone()],
                version: ChannelVersion::empty(), // missing
            },
        }
    };
}

pub fn channel_from_event(event: &IbcEvent) -> Option<IdentifiedChannelEnd> {
    match event {
        IbcEvent::OpenInitChannel(ev) => Some(event_to_channel!(ev, State::Init)),
        IbcEvent::OpenTryChannel(ev) => Some(event_to_channel!(ev, State::TryOpen)),
        IbcEvent::OpenAckChannel(ev) => Some(event_to_channel!(ev, State::Open)),
        IbcEvent::OpenConfirmChannel(ev) => Some(event_to_channel!(ev, State::Open)),
        _ => None,
    }
}
