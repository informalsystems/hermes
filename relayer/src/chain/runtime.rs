use std::{sync::Arc, thread};

use crossbeam_channel as channel;
use tokio::runtime::Runtime as TokioRuntime;

use ibc::{
    events::IbcEvent,
    ics02_client::{
        client_consensus::ConsensusState, client_state::ClientState, header::AnyHeader,
        header::Header,
    },
    ics03_connection::{connection::ConnectionEnd, version::Version},
    ics04_channel::{
        channel::{ChannelEnd, QueryPacketEventDataRequest},
        packet::{PacketMsgType, Sequence},
    },
    ics23_commitment::commitment::CommitmentPrefix,
    ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
    proofs::Proofs,
    signer::Signer,
    Height,
};
use ibc_proto::ibc::core::{
    channel::v1::{
        PacketState, QueryNextSequenceReceiveRequest, QueryPacketAcknowledgementsRequest,
        QueryPacketCommitmentsRequest, QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
    },
    commitment::v1::MerkleProof,
};

use crate::{
    config::ChainConfig,
    connection::ConnectionMsgType,
    error::{Error, Kind},
    event::{bus::EventBus, monitor::EventBatch},
    keyring::store::KeyEntry,
    light_client::LightClient,
};

use super::{
    handle::{ChainHandle, ChainRequest, ProdChainHandle, ReplyTo, Subscription},
    Chain,
};
use ibc::ics02_client::client_consensus::AnyConsensusState;
use ibc::ics02_client::client_state::AnyClientState;

pub struct Threads {
    pub light_client: Option<thread::JoinHandle<()>>,
    pub chain_runtime: thread::JoinHandle<()>,
    pub event_monitor: Option<thread::JoinHandle<()>>,
}

pub struct ChainRuntime<C: Chain> {
    /// The specific chain this runtime runs against
    chain: C,

    /// The sender side of a channel to this runtime. Any `ChainHandle` can use this to send
    /// chain requests to this runtime
    request_sender: channel::Sender<ChainRequest>,

    /// The receiving side of a channel to this runtime. The runtime consumes chain requests coming
    /// in through this channel.
    request_receiver: channel::Receiver<ChainRequest>,

    /// An event bus, for broadcasting events that this runtime receives (via `event_receiver`) to subscribers
    event_bus: EventBus<Arc<EventBatch>>,

    /// Receiver channel from the event bus
    event_receiver: channel::Receiver<EventBatch>,

    /// A handle to the light client
    light_client: Box<dyn LightClient<C>>,

    #[allow(dead_code)]
    rt: Arc<TokioRuntime>, // Making this future-proof, so we keep the runtime around.
}

impl<C: Chain + Send + 'static> ChainRuntime<C> {
    /// Spawns a new runtime for a specific Chain implementation.
    pub fn spawn(config: ChainConfig) -> Result<(Box<dyn ChainHandle>, Threads), Error> {
        let rt = Arc::new(TokioRuntime::new().map_err(|e| Kind::Io.context(e))?);

        // Similar to `from_config`.
        let chain = C::bootstrap(config, rt.clone())?;

        // Start the light client
        let (light_client_handler, light_client_thread) = chain.init_light_client()?;

        // Start the event monitor
        let (event_receiver, event_monitor_thread) = chain.init_event_monitor(rt.clone())?;

        // Instantiate & spawn the runtime
        let (handle, runtime_thread) = Self::init(chain, light_client_handler, event_receiver, rt);

        let threads = Threads {
            light_client: light_client_thread,
            chain_runtime: runtime_thread,
            event_monitor: event_monitor_thread,
        };

        Ok((handle, threads))
    }

    /// Initializes a runtime for a given chain, and spawns the associated thread
    fn init(
        chain: C,
        light_client: Box<dyn LightClient<C>>,
        event_receiver: channel::Receiver<EventBatch>,
        rt: Arc<TokioRuntime>,
    ) -> (Box<dyn ChainHandle>, thread::JoinHandle<()>) {
        let chain_runtime = Self::new(chain, light_client, event_receiver, rt);

        // Get a handle to the runtime
        let handle = chain_runtime.handle();

        // Spawn the runtime & return
        let thread = thread::spawn(move || chain_runtime.run().unwrap());

        (handle, thread)
    }

    /// Basic constructor
    fn new(
        chain: C,
        light_client: Box<dyn LightClient<C>>,
        event_receiver: channel::Receiver<EventBatch>,
        rt: Arc<TokioRuntime>,
    ) -> Self {
        let (request_sender, request_receiver) = channel::unbounded::<ChainRequest>();

        Self {
            rt,
            chain,
            request_sender,
            request_receiver,
            event_bus: EventBus::new(),
            event_receiver,
            light_client,
        }
    }

    pub fn handle(&self) -> Box<dyn ChainHandle> {
        let chain_id = self.chain.id().clone();
        let sender = self.request_sender.clone();

        Box::new(ProdChainHandle::new(chain_id, sender))
    }

    fn run(mut self) -> Result<(), Error> {
        loop {
            channel::select! {
                recv(self.event_receiver) -> event_batch => {
                    if let Ok(event_batch) = event_batch {
                        self.event_bus
                            .broadcast(Arc::new(event_batch))
                            .map_err(|e| Kind::Channel.context(e))?;
                    } else {
                        // TODO: Handle error
                    }
                },
                recv(self.request_receiver) -> event => {
                    match event {
                        Ok(ChainRequest::Terminate { reply_to }) => {
                            reply_to.send(Ok(())).map_err(|_| Kind::Channel)?;
                            break;
                        }

                        Ok(ChainRequest::Subscribe { reply_to }) => {
                            self.subscribe(reply_to)?
                        },

                        Ok(ChainRequest::SendMsgs { proto_msgs, reply_to }) => {
                            self.send_msgs(proto_msgs, reply_to)?
                        },

                        Ok(ChainRequest::GetMinimalSet { from, to, reply_to }) => {
                            self.get_minimal_set(from, to, reply_to)?
                        }

                        Ok(ChainRequest::Signer { reply_to }) => {
                            self.get_signer(reply_to)?
                        }

                        Ok(ChainRequest::Key { reply_to }) => {
                            self.get_key(reply_to)?
                        }

                        Ok(ChainRequest::ModuleVersion { port_id, reply_to }) => {
                            self.module_version(port_id, reply_to)?
                        }

                        Ok(ChainRequest::BuildHeader { trusted_height, target_height, reply_to }) => {
                            self.build_header(trusted_height, target_height, reply_to)?
                        }

                        Ok(ChainRequest::BuildClientState { height, reply_to }) => {
                            self.build_client_state(height, reply_to)?
                        }

                        Ok(ChainRequest::BuildConsensusState { height, reply_to }) => {
                            self.build_consensus_state(height, reply_to)?
                        }

                        Ok(ChainRequest::BuildConnectionProofsAndClientState { message_type, connection_id, client_id, height, reply_to }) => {
                            self.build_connection_proofs_and_client_state(message_type, connection_id, client_id, height, reply_to)?
                        },

                        Ok(ChainRequest::BuildChannelProofs { port_id, channel_id, height, reply_to }) => {
                            self.build_channel_proofs(port_id, channel_id, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryLatestHeight { reply_to }) => {
                            self.query_latest_height(reply_to)?
                        }

                        Ok(ChainRequest::QueryClientState { client_id, height, reply_to }) => {
                            self.query_client_state(client_id, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryCommitmentPrefix { reply_to }) => {
                            self.query_commitment_prefix(reply_to)?
                        },

                        Ok(ChainRequest::QueryCompatibleVersions { reply_to }) => {
                            self.query_compatible_versions(reply_to)?
                        },

                        Ok(ChainRequest::QueryConnection { connection_id, height, reply_to }) => {
                            self.query_connection(connection_id, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryChannel { port_id, channel_id, height, reply_to }) => {
                            self.query_channel(port_id, channel_id, height, reply_to)?
                        },

                        Ok(ChainRequest::ProvenClientState { client_id, height, reply_to }) => {
                            self.proven_client_state(client_id, height, reply_to)?
                        },

                        Ok(ChainRequest::ProvenConnection { connection_id, height, reply_to }) => {
                            self.proven_connection(connection_id, height, reply_to)?
                        },

                        Ok(ChainRequest::ProvenClientConsensus { client_id, consensus_height, height, reply_to }) => {
                            self.proven_client_consensus(client_id, consensus_height, height, reply_to)?
                        },

                        Ok(ChainRequest::BuildPacketProofs { packet_type, port_id, channel_id, sequence, height, reply_to }) => {
                            self.build_packet_proofs(packet_type, port_id, channel_id, sequence, height, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketCommitments { request, reply_to }) => {
                            self.query_packet_commitments(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryUnreceivedPackets { request, reply_to }) => {
                            self.query_unreceived_packets(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketAcknowledgement { request, reply_to }) => {
                            self.query_packet_acknowledgements(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to }) => {
                            self.query_unreceived_acknowledgement(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryNextSequenceReceive { request, reply_to }) => {
                            self.query_next_sequence_receive(request, reply_to)?
                        },

                        Ok(ChainRequest::QueryPacketEventData { request, reply_to }) => {
                            self.query_txs(request, reply_to)?
                        },

                        Err(_e) => todo!(), // TODO: Handle error?
                    }
                },
            }
        }

        Ok(())
    }

    fn subscribe(&mut self, reply_to: ReplyTo<Subscription>) -> Result<(), Error> {
        let subscription = self.event_bus.subscribe();

        reply_to
            .send(Ok(subscription))
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn send_msgs(
        &mut self,
        proto_msgs: Vec<prost_types::Any>,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    ) -> Result<(), Error> {
        let result = self.chain.send_msgs(proto_msgs);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_latest_height(&self, reply_to: ReplyTo<Height>) -> Result<(), Error> {
        let latest_height = self.chain.query_latest_height();

        reply_to
            .send(latest_height)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn get_minimal_set(
        &self,
        _from: Height,
        _to: Height,
        _reply_to: ReplyTo<Vec<AnyHeader>>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn get_signer(&mut self, reply_to: ReplyTo<Signer>) -> Result<(), Error> {
        let result = self.chain.get_signer();

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn get_key(&mut self, reply_to: ReplyTo<KeyEntry>) -> Result<(), Error> {
        let result = self.chain.get_key();

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn module_version(&self, port_id: PortId, reply_to: ReplyTo<String>) -> Result<(), Error> {
        let result = self.chain.query_module_version(&port_id);

        reply_to
            .send(Ok(result))
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        reply_to: ReplyTo<AnyHeader>,
    ) -> Result<(), Error> {
        let header = {
            // Get the light block at trusted_height from the chain.
            // TODO - it is possible that trusted_height is smaller than the current latest trusted
            // height and this results in error here.
            // Note: This happens if there are multiple on-chain clients at different latest heights
            let trusted_light_block = self.light_client.verify_to_target(trusted_height)?;

            // Get the light block at target_height from chain.
            let target_light_block = self.light_client.verify_to_target(target_height)?;

            let header = self
                .chain
                .build_header(trusted_light_block, target_light_block)?;

            Ok(header.wrap_any())
        };

        reply_to
            .send(header)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    /// Constructs a client state for the given height
    fn build_client_state(
        &self,
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        let client_state = self
            .chain
            .build_client_state(height)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(client_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    /// Constructs a consensus state for the given height
    fn build_consensus_state(
        &self,
        height: Height,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        let latest_light_block = self.light_client.verify_to_target(height)?;

        let consensus_state = self
            .chain
            .build_consensus_state(latest_light_block)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(consensus_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
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

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_client_state(
        &self,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        let client_state = self
            .chain
            .query_client_state(&client_id, height)
            .map(|cs| cs.wrap_any());

        reply_to
            .send(client_state)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_commitment_prefix(&self, reply_to: ReplyTo<CommitmentPrefix>) -> Result<(), Error> {
        let prefix = self.chain.query_commitment_prefix();

        reply_to
            .send(prefix)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_compatible_versions(&self, reply_to: ReplyTo<Vec<Version>>) -> Result<(), Error> {
        let versions = self.chain.query_compatible_versions();

        reply_to
            .send(versions)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_connection(
        &self,
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<ConnectionEnd>,
    ) -> Result<(), Error> {
        let connection_end = self.chain.query_connection(&connection_id, height);

        reply_to
            .send(connection_end)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_channel(
        &self,
        port_id: PortId,
        channel_id: ChannelId,
        height: Height,
        reply_to: ReplyTo<ChannelEnd>,
    ) -> Result<(), Error> {
        let result = self.chain.query_channel(&port_id, &channel_id, height);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_client_state(
        &self,
        client_id: ClientId,
        height: Height,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .proven_client_state(&client_id, height)
            .map(|(cs, mp)| (cs.wrap_any(), mp));

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_connection(
        &self,
        connection_id: ConnectionId,
        height: Height,
        reply_to: ReplyTo<(ConnectionEnd, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self.chain.proven_connection(&connection_id, height);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn proven_client_consensus(
        &self,
        client_id: ClientId,
        consensus_height: Height,
        height: Height,
        reply_to: ReplyTo<(AnyConsensusState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self
            .chain
            .proven_client_consensus(&client_id, consensus_height, height)
            .map(|(cs, mp)| (cs.wrap_any(), mp));

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
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

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
        height: Height,
        reply_to: ReplyTo<(Vec<u8>, Proofs)>,
    ) -> Result<(), Error> {
        let result =
            self.chain
                .build_packet_proofs(packet_type, port_id, channel_id, sequence, height);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
        reply_to: ReplyTo<(Vec<PacketState>, Height)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_commitments(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
        reply_to: ReplyTo<Vec<u64>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_unreceived_packets(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
        reply_to: ReplyTo<(Vec<PacketState>, Height)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_acknowledgements(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_unreceived_acknowledgement(
        &self,
        request: QueryUnreceivedAcksRequest,
        reply_to: ReplyTo<Vec<u64>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_unreceived_acknowledgements(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        reply_to: ReplyTo<Sequence>,
    ) -> Result<(), Error> {
        let result = self.chain.query_next_sequence_receive(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn query_txs(
        &self,
        request: QueryPacketEventDataRequest,
        reply_to: ReplyTo<Vec<IbcEvent>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_txs(request);

        reply_to
            .send(result)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }
}
