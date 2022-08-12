use alloc::sync::Arc;
use std::thread;

use crossbeam_channel as channel;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::error;

use ibc::{
    core::{
        ics02_client::{
            client_consensus::{AnyConsensusState, AnyConsensusStateWithHeight, ConsensusState},
            client_state::{AnyClientState, ClientState, IdentifiedAnyClientState},
            events::UpdateClient,
            header::{AnyHeader, Header},
            misbehaviour::MisbehaviourEvidence,
        },
        ics03_connection::{
            connection::{ConnectionEnd, IdentifiedConnectionEnd},
            version::Version,
        },
        ics04_channel::{
            channel::{ChannelEnd, IdentifiedChannelEnd},
            packet::{PacketMsgType, Sequence},
        },
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
    },
    events::IbcEvent,
    proofs::Proofs,
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    config::ChainConfig,
    connection::ConnectionMsgType,
    denom::DenomTrace,
    error::Error,
    event::{
        bus::EventBus,
        monitor::{EventBatch, EventReceiver, MonitorCmd, Result as MonitorResult, TxMonitorCmd},
    },
    keyring::KeyEntry,
};

use super::{
    client::ClientSettings,
    endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
    handle::{ChainHandle, ChainRequest, ReplyTo, Subscription},
    requests::{
        IncludeProof, QueryBlockRequest, QueryChannelClientStateRequest, QueryChannelRequest,
        QueryChannelsRequest, QueryClientConnectionsRequest, QueryClientStateRequest,
        QueryClientStatesRequest, QueryConnectionChannelsRequest, QueryConnectionRequest,
        QueryConnectionsRequest, QueryConsensusStateRequest, QueryConsensusStatesRequest,
        QueryHostConsensusStateRequest, QueryNextSequenceReceiveRequest,
        QueryPacketAcknowledgementRequest, QueryPacketAcknowledgementsRequest,
        QueryPacketCommitmentRequest, QueryPacketCommitmentsRequest, QueryPacketReceiptRequest,
        QueryTxRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
        QueryUpgradedClientStateRequest, QueryUpgradedConsensusStateRequest,
    },
    tracking::TrackedMsgs,
};

pub struct Threads {
    pub chain_runtime: thread::JoinHandle<()>,
    pub event_monitor: Option<thread::JoinHandle<()>>,
}

#[derive(Debug)]
pub enum EventMonitorCtrl {
    None {
        /// Empty channel for when the None case
        never: EventReceiver,
    },
    Live {
        /// Receiver channel from the event bus
        event_receiver: EventReceiver,

        /// Sender channel to terminate the event monitor
        tx_monitor_cmd: TxMonitorCmd,
    },
}

impl EventMonitorCtrl {
    pub fn none() -> Self {
        Self::None {
            never: channel::never(),
        }
    }

    pub fn live(event_receiver: EventReceiver, tx_monitor_cmd: TxMonitorCmd) -> Self {
        Self::Live {
            event_receiver,
            tx_monitor_cmd,
        }
    }

    pub fn enable(&mut self, event_receiver: EventReceiver, tx_monitor_cmd: TxMonitorCmd) {
        *self = Self::live(event_receiver, tx_monitor_cmd);
    }

    pub fn recv(&self) -> &EventReceiver {
        match self {
            Self::None { ref never } => never,
            Self::Live {
                ref event_receiver, ..
            } => event_receiver,
        }
    }

    pub fn shutdown(&self) -> Result<(), Error> {
        match self {
            Self::None { .. } => Ok(()),
            Self::Live {
                ref tx_monitor_cmd, ..
            } => tx_monitor_cmd
                .send(MonitorCmd::Shutdown)
                .map_err(Error::send),
        }
    }

    pub fn is_live(&self) -> bool {
        matches!(self, Self::Live { .. })
    }
}

pub struct ChainRuntime<Endpoint: ChainEndpoint> {
    /// The specific chain this runtime runs against
    chain: Endpoint,

    /// The sender side of a channel to this runtime. Any `ChainHandle` can use this to send
    /// chain requests to this runtime
    request_sender: channel::Sender<ChainRequest>,

    /// The receiving side of a channel to this runtime. The runtime consumes chain requests coming
    /// in through this channel.
    request_receiver: channel::Receiver<ChainRequest>,

    /// An event bus, for broadcasting events that this runtime receives (via `event_receiver`) to subscribers
    event_bus: EventBus<Arc<MonitorResult<EventBatch>>>,

    /// Interface to the event monitor
    event_monitor_ctrl: EventMonitorCtrl,

    #[allow(dead_code)]
    rt: Arc<TokioRuntime>, // Making this future-proof, so we keep the runtime around.
}

impl<Endpoint> ChainRuntime<Endpoint>
where
    Endpoint: ChainEndpoint + Send + 'static,
{
    /// Spawns a new runtime for a specific Chain implementation.
    pub fn spawn<Handle: ChainHandle>(
        config: ChainConfig,
        rt: Arc<TokioRuntime>,
    ) -> Result<Handle, Error> {
        // Similar to `from_config`.
        let chain = Endpoint::bootstrap(config, rt.clone())?;

        // Instantiate & spawn the runtime
        let (handle, _) = Self::init(chain, rt);

        Ok(handle)
    }

    /// Initializes a runtime for a given chain, and spawns the associated thread
    fn init<Handle: ChainHandle>(
        chain: Endpoint,
        rt: Arc<TokioRuntime>,
    ) -> (Handle, thread::JoinHandle<()>) {
        let chain_runtime = Self::new(chain, rt);

        // Get a handle to the runtime
        let handle: Handle = chain_runtime.handle();

        // Spawn the runtime & return
        let id = handle.id();
        let thread = thread::spawn(move || {
            if let Err(e) = chain_runtime.run() {
                error!("failed to start runtime for chain '{}': {}", id, e);
            }
        });

        (handle, thread)
    }

    /// Basic constructor
    fn new(chain: Endpoint, rt: Arc<TokioRuntime>) -> Self {
        let (request_sender, request_receiver) = channel::unbounded::<ChainRequest>();

        Self {
            rt,
            chain,
            request_sender,
            request_receiver,
            event_bus: EventBus::new(),
            event_monitor_ctrl: EventMonitorCtrl::none(),
        }
    }

    pub fn handle<Handle: ChainHandle>(&self) -> Handle {
        let chain_id = ChainEndpoint::id(&self.chain).clone();
        let sender = self.request_sender.clone();

        Handle::new(chain_id, sender)
    }

    fn run(mut self) -> Result<(), Error> {
        loop {
            channel::select! {
                recv(self.event_monitor_ctrl.recv()) -> event_batch => {
                    match event_batch {
                        Ok(event_batch) => {
                            self.event_bus
                                .broadcast(Arc::new(event_batch));
                        },
                        Err(e) => {
                            error!("received error via event bus: {}", e);
                            return Err(Error::channel_receive(e));
                        },
                    }
                },
                recv(self.request_receiver) -> event => {
                    match event {
                        Ok(ChainRequest::Shutdown { reply_to }) => {
                            self.event_monitor_ctrl.shutdown()?;

                            let res = self.chain.shutdown();
                            reply_to.send(res)
                                .map_err(Error::send)?;

                            break;
                        },

                        Ok(ChainRequest::HealthCheck { reply_to }) => {
                            self.health_check(reply_to)?
                        },

                        Ok(ChainRequest::Subscribe { reply_to }) => {
                            self.subscribe(reply_to)?
                        },

                        Ok(ChainRequest::SendMessagesAndWaitCommit { tracked_msgs, reply_to }) => {
                            self.send_messages_and_wait_commit(tracked_msgs, reply_to)?
                        },

                        Ok(ChainRequest::SendMessagesAndWaitCheckTx { tracked_msgs, reply_to }) => {
                            self.send_messages_and_wait_check_tx(tracked_msgs, reply_to)?
                        },

                        Ok(ChainRequest::Signer { reply_to }) => {
                            self.get_signer(reply_to)?
                        },

                        Ok(ChainRequest::Config { reply_to }) => {
                            self.get_config(reply_to)?
                        },

                        Ok(ChainRequest::GetKey { reply_to }) => {
                            self.get_key(reply_to)?
                        },

                        Ok(ChainRequest::AddKey { key_name, key, reply_to }) => {
                            self.add_key(key_name, key, reply_to)?
                        },

                        Ok(ChainRequest::IbcVersion { reply_to }) => {
                            self.ibc_version(reply_to)?
                        },

                        Ok(ChainRequest::BuildHeader { trusted_height, target_height, client_state, reply_to }) => {
                            self.build_header(trusted_height, target_height, client_state, reply_to)?
                        },

                        Ok(ChainRequest::BuildClientState { height, settings, reply_to }) => {
                            self.build_client_state(height, settings, reply_to)?
                        },

                        Ok(ChainRequest::BuildConsensusState { trusted, target, client_state, reply_to }) => {
                            self.build_consensus_state(trusted, target, client_state, reply_to)?
                        },

                       Ok(ChainRequest::BuildMisbehaviour { client_state, update_event, reply_to }) => {
                            self.check_misbehaviour(update_event, client_state, reply_to)?
                        },

                        Ok(ChainRequest::BuildConnectionProofsAndClientState { message_type, connection_id, client_id, height, reply_to }) => {
                            self.build_connection_proofs_and_client_state(message_type, connection_id, client_id, height, reply_to)?
                        },

                        Ok(ChainRequest::BuildChannelProofs { port_id, channel_id, height, reply_to }) => {
                            self.build_channel_proofs(port_id, channel_id, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryBalance { key_name, reply_to }) => {
                            self.query_balance(key_name, reply_to)?
                        },

                        Ok(ChainRequest::QueryDenomTrace { hash, reply_to }) => {
                            self.query_denom_trace(hash, reply_to)?
                        },

                        Ok(ChainRequest::QueryApplicationStatus { reply_to }) => {
                            self.query_application_status(reply_to)?
                        },

                        Ok(ChainRequest::QueryClients { request, reply_to }) => {
                            self.query_clients(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryClientConnections { request, reply_to }) => {
                            self.query_client_connections(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryClientState { request, include_proof, reply_to }) => {
                            self.query_client_state(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryConsensusStates { request, reply_to }) => {
                            self.query_consensus_states(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryConsensusState { request, include_proof, reply_to }) => {
                            self.query_consensus_state(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryUpgradedClientState { request, reply_to }) => {
                            self.query_upgraded_client_state(request, reply_to)?
                        },

                       Ok(ChainRequest::QueryUpgradedConsensusState { request, reply_to }) => {
                            self.query_upgraded_consensus_state(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryCommitmentPrefix { reply_to }) => {
                            self.query_commitment_prefix(reply_to)?
                        },

                        Ok(ChainRequest::QueryCompatibleVersions { reply_to }) => {
                            self.query_compatible_versions(reply_to)?
                        },

                        Ok(ChainRequest::QueryConnection { request, include_proof, reply_to }) => {
                            self.query_connection(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryConnections { request, reply_to }) => {
                            self.query_connections(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryConnectionChannels { request, reply_to }) => {
                            self.query_connection_channels(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryChannels { request, reply_to }) => {
                            self.query_channels(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryChannel { request, include_proof, reply_to }) => {
                            self.query_channel(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryChannelClientState { request, reply_to }) => {
                            self.query_channel_client_state(request, reply_to)?
                        },

                        Ok(ChainRequest::BuildPacketProofs { packet_type, port_id, channel_id, sequence, height, reply_to }) => {
                            self.build_packet_proofs(packet_type, port_id, channel_id, sequence, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketCommitment { request, include_proof, reply_to }) => {
                            self.query_packet_commitment(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketCommitments { request, reply_to }) => {
                            self.query_packet_commitments(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketReceipt { request, include_proof, reply_to }) => {
                            self.query_packet_receipt(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryUnreceivedPackets { request, reply_to }) => {
                            self.query_unreceived_packets(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketAcknowledgement { request, include_proof, reply_to }) => {
                            self.query_packet_acknowledgement(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketAcknowledgements { request, reply_to }) => {
                            self.query_packet_acknowledgements(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to }) => {
                            self.query_unreceived_acknowledgement(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryNextSequenceReceive { request, include_proof, reply_to }) => {
                            self.query_next_sequence_receive(request, include_proof, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketEventDataFromTxs { request, reply_to }) => {
                            self.query_txs(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketEventDataFromBlocks { request, reply_to }) => {
                            self.query_blocks(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryHostConsensusState { request, reply_to }) => {
                            self.query_host_consensus_state(request, reply_to)?
                        },

                        Err(e) => error!("received error via chain request channel: {}", e),
                    }
                },
            }
        }

        Ok(())
    }

    fn health_check(&mut self, reply_to: ReplyTo<HealthCheck>) -> Result<(), Error> {
        let result = self.chain.health_check();
        reply_to.send(result).map_err(Error::send)
    }

    fn subscribe(&mut self, reply_to: ReplyTo<Subscription>) -> Result<(), Error> {
        if !self.event_monitor_ctrl.is_live() {
            self.enable_event_monitor()?;
        }

        let subscription = self.event_bus.subscribe();
        reply_to.send(Ok(subscription)).map_err(Error::send)
    }

    fn enable_event_monitor(&mut self) -> Result<(), Error> {
        let (event_receiver, tx_monitor_cmd) = self.chain.init_event_monitor(self.rt.clone())?;

        self.event_monitor_ctrl
            .enable(event_receiver, tx_monitor_cmd);

        Ok(())
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    ) -> Result<(), Error> {
        let result = self.chain.send_messages_and_wait_commit(tracked_msgs);
        reply_to.send(result).map_err(Error::send)
    }

    fn send_messages_and_wait_check_tx(
        &mut self,
        tracked_msgs: TrackedMsgs,
        reply_to: ReplyTo<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>>,
    ) -> Result<(), Error> {
        let result = self.chain.send_messages_and_wait_check_tx(tracked_msgs);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_balance(
        &self,
        key_name: Option<String>,
        reply_to: ReplyTo<Balance>,
    ) -> Result<(), Error> {
        let balance = self.chain.query_balance(key_name);
        reply_to.send(balance).map_err(Error::send)
    }

    fn query_denom_trace(&self, hash: String, reply_to: ReplyTo<DenomTrace>) -> Result<(), Error> {
        let denom_trace = self.chain.query_denom_trace(hash);
        reply_to.send(denom_trace).map_err(Error::send)
    }

    fn query_application_status(&self, reply_to: ReplyTo<ChainStatus>) -> Result<(), Error> {
        let latest_timestamp = self.chain.query_application_status();
        reply_to.send(latest_timestamp).map_err(Error::send)
    }

    fn get_signer(&mut self, reply_to: ReplyTo<Signer>) -> Result<(), Error> {
        let result = self.chain.get_signer();
        reply_to.send(result).map_err(Error::send)
    }

    fn get_config(&self, reply_to: ReplyTo<ChainConfig>) -> Result<(), Error> {
        let result = Ok(self.chain.config());
        reply_to.send(result).map_err(Error::send)
    }

    fn get_key(&mut self, reply_to: ReplyTo<KeyEntry>) -> Result<(), Error> {
        let result = self.chain.get_key();
        reply_to.send(result).map_err(Error::send)
    }

    fn add_key(
        &mut self,
        key_name: String,
        key: KeyEntry,
        reply_to: ReplyTo<()>,
    ) -> Result<(), Error> {
        let result = self.chain.add_key(&key_name, key);
        reply_to.send(result).map_err(Error::send)
    }

    fn ibc_version(&mut self, reply_to: ReplyTo<Option<semver::Version>>) -> Result<(), Error> {
        let result = self.chain.ibc_version();
        reply_to.send(result).map_err(Error::send)
    }

    fn build_header(
        &mut self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
        reply_to: ReplyTo<(AnyHeader, Vec<AnyHeader>)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .build_header(trusted_height, target_height, &client_state)
            .map(|(header, support)| {
                let header = header.wrap_any();
                let support = support.into_iter().map(|h| h.wrap_any()).collect();
                (header, support)
            });

        reply_to.send(result).map_err(Error::send)
    }

    /// Constructs a client state for the given height
    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        let client_state = self
            .chain
            .build_client_state(height, settings)
            .map(|cs| cs.wrap_any());

        reply_to.send(client_state).map_err(Error::send)
    }

    /// Constructs a consensus state for the given height
    fn build_consensus_state(
        &mut self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        let verified = self.chain.verify_header(trusted, target, &client_state)?;

        let consensus_state = self
            .chain
            .build_consensus_state(verified)
            .map(|cs| cs.wrap_any());

        reply_to.send(consensus_state).map_err(Error::send)
    }

    /// Constructs AnyMisbehaviour for the update event
    fn check_misbehaviour(
        &mut self,
        update_event: UpdateClient,
        client_state: AnyClientState,
        reply_to: ReplyTo<Option<MisbehaviourEvidence>>,
    ) -> Result<(), Error> {
        let misbehaviour = self.chain.check_misbehaviour(&update_event, &client_state);

        reply_to.send(misbehaviour).map_err(Error::send)
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: ConnectionId,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(Option<AnyClientState>, Proofs)>,
    ) -> Result<(), Error> {
        let result = self.chain.build_connection_proofs_and_client_state(
            message_type,
            &connection_id,
            &client_id,
            height,
        );

        let result = result
            .map(|(opt_client_state, proofs)| (opt_client_state.map(|cs| cs.wrap_any()), proofs));

        reply_to.send(result).map_err(Error::send)
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
        reply_to: ReplyTo<Vec<IdentifiedAnyClientState>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_clients(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
        reply_to: ReplyTo<Vec<ConnectionId>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_client_connections(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(AnyClientState, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let res = self
            .chain
            .query_client_state(request, include_proof)
            .map(|(cs, proof)| (cs.wrap_any(), proof));

        reply_to.send(res).map_err(Error::send)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .query_upgraded_client_state(request)
            .map(|(cl, proof)| (cl.wrap_any(), proof));

        reply_to.send(result).map_err(Error::send)
    }

    fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
        reply_to: ReplyTo<Vec<AnyConsensusStateWithHeight>>,
    ) -> Result<(), Error> {
        let consensus_states = self.chain.query_consensus_states(request);
        reply_to.send(consensus_states).map_err(Error::send)
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(AnyConsensusState, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let res = self.chain.query_consensus_state(request, include_proof);

        reply_to.send(res).map_err(Error::send)
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .query_upgraded_consensus_state(request)
            .map(|(cs, proof)| (cs.wrap_any(), proof));

        reply_to.send(result).map_err(Error::send)
    }

    fn query_commitment_prefix(&self, reply_to: ReplyTo<CommitmentPrefix>) -> Result<(), Error> {
        let prefix = self.chain.query_commitment_prefix();
        reply_to.send(prefix).map_err(Error::send)
    }

    fn query_compatible_versions(&self, reply_to: ReplyTo<Vec<Version>>) -> Result<(), Error> {
        let versions = self.chain.query_compatible_versions();
        reply_to.send(versions).map_err(Error::send)
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(ConnectionEnd, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let connection_end = self.chain.query_connection(request, include_proof);
        reply_to.send(connection_end).map_err(Error::send)
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
        reply_to: ReplyTo<Vec<IdentifiedConnectionEnd>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_connections(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
        reply_to: ReplyTo<Vec<IdentifiedChannelEnd>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_connection_channels(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
        reply_to: ReplyTo<Vec<IdentifiedChannelEnd>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_channels(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(ChannelEnd, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_channel(request, include_proof);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
        reply_to: ReplyTo<Option<IdentifiedAnyClientState>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_channel_client_state(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn build_channel_proofs(
        &self,
        port_id: PortId,
        channel_id: ChannelId,
        height: Height,
        reply_to: ReplyTo<Proofs>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .build_channel_proofs(&port_id, &channel_id, height);

        reply_to.send(result).map_err(Error::send)
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: Height,
        reply_to: ReplyTo<Proofs>,
    ) -> Result<(), Error> {
        let result =
            self.chain
                .build_packet_proofs(packet_type, port_id, channel_id, sequence, height);

        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_commitment(request, include_proof);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_commitments(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_receipt(request, include_proof);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_unreceived_packets(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Vec<u8>, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .query_packet_acknowledgement(request, include_proof);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
        reply_to: ReplyTo<(Vec<Sequence>, Height)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_acknowledgements(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
        reply_to: ReplyTo<Vec<Sequence>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_unreceived_acknowledgements(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
        reply_to: ReplyTo<(Sequence, Option<MerkleProof>)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .query_next_sequence_receive(request, include_proof);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_txs(
        &self,
        request: QueryTxRequest,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_txs(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_blocks(
        &self,
        request: QueryBlockRequest,
        reply_to: ReplyTo<(Vec<IbcEvent>, Vec<IbcEvent>)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_blocks(request);

        reply_to.send(result).map_err(Error::send)?;

        Ok(())
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .query_host_consensus_state(request)
            .map(|h| h.wrap_any());

        reply_to.send(result).map_err(Error::send)?;

        Ok(())
    }
}
