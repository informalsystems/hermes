use std::{
    sync::{Arc, Mutex},
    thread,
};

use crossbeam_channel as channel;

use tokio::runtime::Runtime as TokioRuntime;

use ibc::{
    ics02_client::{
        client_def::{AnyClientState, AnyConsensusState, AnyHeader},
        header::Header,
        state::{ClientState, ConsensusState},
    },
    ics03_connection::connection::ConnectionEnd,
    ics04_channel::channel::ChannelEnd,
    ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
    ics24_host::identifier::ChannelId,
    ics24_host::identifier::PortId,
    ics24_host::identifier::{ClientId, ConnectionId},
    ics24_host::Path,
    proofs::Proofs,
    Height,
};

// FIXME: the handle should not depend on tendermint-specific types
use tendermint::account::Id as AccountId;

// use crate::foreign_client::ForeignClient;

use crate::{
    config::ChainConfig,
    connection::ConnectionMsgType,
    error::{Error, Kind},
    event::{
        bus::EventBus,
        monitor::{EventBatch, EventMonitor},
    },
    keyring::store::KeyEntry,
    light_client::{tendermint::LightClient as TMLightClient, LightClient},
};

use super::{
    handle::{ChainHandle, HandleInput, ProdChainHandle, ReplyTo, Subscription},
    Chain, CosmosSDKChain, QueryResponse,
};
use ibc_proto::ibc::core::channel::v1::{
    PacketAckCommitment, QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

pub struct Threads {
    pub light_client: thread::JoinHandle<()>,
    pub chain_runtime: thread::JoinHandle<()>,
    pub event_monitor: thread::JoinHandle<()>,
}

pub struct ChainRuntime<C: Chain> {
    chain: C,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
    event_bus: EventBus<Arc<EventBatch>>,
    event_receiver: channel::Receiver<EventBatch>,
    light_client: Box<dyn LightClient<C>>,

    #[allow(dead_code)]
    rt: Arc<Mutex<TokioRuntime>>,
}

impl ChainRuntime<CosmosSDKChain> {
    pub fn cosmos_sdk(
        config: ChainConfig,
        light_client: TMLightClient,
        event_receiver: channel::Receiver<EventBatch>,
        rt: Arc<Mutex<TokioRuntime>>,
    ) -> Result<Self, Error> {
        let chain = CosmosSDKChain::from_config(config, rt.clone())?;
        Ok(Self::new(chain, light_client, event_receiver, rt))
    }

    // TODO: Make this work for a generic Chain
    pub fn spawn(config: ChainConfig) -> Result<(impl ChainHandle, Threads), Error> {
        let rt = Arc::new(Mutex::new(
            TokioRuntime::new().map_err(|e| Kind::Io.context(e))?,
        ));

        // Initialize the light clients
        let (light_client, supervisor) = TMLightClient::from_config(&config, true)?;

        // Spawn the light clients
        let light_client_thread = thread::spawn(move || supervisor.run().unwrap());

        let (mut event_monitor, event_receiver) =
            EventMonitor::new(config.id.clone(), config.rpc_addr.clone(), rt.clone())?;

        // FIXME: Only connect/subscribe on demand + deal with error
        event_monitor.subscribe().unwrap();

        // Spawn the event monitor
        let event_monitor_thread = thread::spawn(move || event_monitor.run());

        // Initialize the source and destination chain runtimes
        let chain_runtime = Self::cosmos_sdk(config, light_client, event_receiver, rt)?;

        // Get a handle to the runtime
        let handle = chain_runtime.handle();

        // Spawn the runtime
        let runtime_thread = thread::spawn(move || chain_runtime.run().unwrap());

        let threads = Threads {
            light_client: light_client_thread,
            chain_runtime: runtime_thread,
            event_monitor: event_monitor_thread,
        };

        Ok((handle, threads))
    }
}

impl<C: Chain> ChainRuntime<C> {
    pub fn new(
        chain: C,
        light_client: impl LightClient<C> + 'static,
        event_receiver: channel::Receiver<EventBatch>,
        rt: Arc<Mutex<TokioRuntime>>,
    ) -> Self {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            rt,
            chain,
            sender,
            receiver,
            event_bus: EventBus::new(),
            event_receiver,
            light_client: Box::new(light_client),
        }
    }

    pub fn handle(&self) -> impl ChainHandle {
        let chain_id = self.chain.id().clone();
        let sender = self.sender.clone();

        ProdChainHandle::new(chain_id, sender)
    }

    pub fn run(mut self) -> Result<(), Error> {
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
                recv(self.receiver) -> event => {
                    match event {
                        Ok(HandleInput::Terminate { reply_to }) => {
                            reply_to.send(Ok(())).map_err(|_| Kind::Channel)?;
                            break;
                        }

                        Ok(HandleInput::Subscribe { reply_to }) => {
                            self.subscribe(reply_to)?
                        },

                        Ok(HandleInput::Query { path, height, prove, reply_to, }) => {
                            self.query(path, height, prove, reply_to)?
                        },

                        Ok(HandleInput::SendTx { proto_msgs, reply_to }) => {
                            self.send_tx(proto_msgs, reply_to)?
                        },

                        Ok(HandleInput::GetMinimalSet { from, to, reply_to }) => {
                            self.get_minimal_set(from, to, reply_to)?
                        }

                        // Ok(HandleInput::GetHeader { height, reply_to }) => {
                        //     self.get_header(height, reply_to)?
                        // }
                        //
                        // Ok(HandleInput::Submit { transaction, reply_to, }) => {
                        //     self.submit(transaction, reply_to)?
                        // },
                        //
                        // Ok(HandleInput::CreatePacket { event, reply_to }) => {
                        //     self.create_packet(event, reply_to)?
                        // }

                        Ok(HandleInput::Signer { reply_to }) => {
                            self.get_signer(reply_to)?
                        }

                        Ok(HandleInput::Key { reply_to }) => {
                            self.get_key(reply_to)?
                        }

                        Ok(HandleInput::ModuleVersion { port_id, reply_to }) => {
                            self.module_version(port_id, reply_to)?
                        }

                        Ok(HandleInput::BuildHeader { trusted_height, target_height, reply_to }) => {
                            self.build_header(trusted_height, target_height, reply_to)?
                        }
                        Ok(HandleInput::BuildClientState { height, reply_to }) => {
                            self.build_client_state(height, reply_to)?
                        }
                        Ok(HandleInput::BuildConsensusState { height, reply_to }) => {
                            self.build_consensus_state(height, reply_to)?
                        }
                        Ok(HandleInput::BuildConnectionProofsAndClientState { message_type, connection_id, client_id, height, reply_to }) => {
                            self.build_connection_proofs_and_client_state(message_type, connection_id, client_id, height, reply_to)?
                        },
                        Ok(HandleInput::BuildChannelProofs { port_id, channel_id, height, reply_to }) => {
                            self.build_channel_proofs(port_id, channel_id, height, reply_to)?
                        },

                        Ok(HandleInput::QueryLatestHeight { reply_to }) => {
                            self.query_latest_height(reply_to)?
                        }
                        Ok(HandleInput::QueryClientState { client_id, height, reply_to }) => {
                            self.query_client_state(client_id, height, reply_to)?
                        },

                        Ok(HandleInput::QueryCommitmentPrefix { reply_to }) => {
                            self.query_commitment_prefix(reply_to)?
                        },

                        Ok(HandleInput::QueryCompatibleVersions { reply_to }) => {
                            self.query_compatible_versions(reply_to)?
                        },

                        Ok(HandleInput::QueryConnection { connection_id, height, reply_to }) => {
                            self.query_connection(connection_id, height, reply_to)?
                        },

                        Ok(HandleInput::QueryChannel { port_id, channel_id, height, reply_to }) => {
                            self.query_channel(port_id, channel_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenClientState { client_id, height, reply_to }) => {
                            self.proven_client_state(client_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenConnection { connection_id, height, reply_to }) => {
                            self.proven_connection(connection_id, height, reply_to)?
                        },

                        Ok(HandleInput::ProvenClientConsensus { client_id, consensus_height, height, reply_to }) => {
                            self.proven_client_consensus(client_id, consensus_height, height, reply_to)?
                        },

                        Ok(HandleInput::QueryPacketCommitments { request, reply_to }) => {
                            self.query_packet_commitments(request, reply_to)?
                        },

                        Ok(HandleInput::QueryUnreceivedPackets { request, reply_to }) => {
                            self.query_unreceived_packets(request, reply_to)?
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

    fn query(
        &self,
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<QueryResponse>,
    ) -> Result<(), Error> {
        if !path.is_provable() & prove {
            reply_to
                .send(Err(Kind::NonProvableData.into()))
                .map_err(|e| Kind::Channel.context(e))?;

            return Ok(());
        }

        let response = self.chain.query(path, height, prove);

        // Verify response proof, if requested.
        if prove {
            dbg!("TODO: implement proof verification."); // TODO: Verify proof
        }

        reply_to
            .send(response)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn send_tx(
        &self,
        proto_msgs: Vec<prost_types::Any>,
        reply_to: ReplyTo<String>,
    ) -> Result<(), Error> {
        let result = self.chain.send_tx(proto_msgs);

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

    // fn get_header(&self, height: Height, reply_to: ReplyTo<AnyHeader>) -> Result<(), Error> {
    //     let light_block = self.light_client.verify_to_target(height);
    //     let header: Result<AnyHeader, _> = todo!(); // light_block.map(|lb| lb.signed_header().wrap_any());

    //     reply_to
    //         .send(header)
    //         .map_err(|e| Kind::Channel.context(e))?;

    //     Ok(())
    // }

    fn get_minimal_set(
        &self,
        _from: Height,
        _to: Height,
        _reply_to: ReplyTo<Vec<AnyHeader>>,
    ) -> Result<(), Error> {
        todo!()
    }

    // fn submit(&self, transaction: EncodedTransaction, reply_to: ReplyTo<()>) -> Result<(), Error> {
    //     todo!()
    // }

    // fn create_packet(&self, event: IBCEvent, reply_to: ReplyTo<Packet>) -> Result<(), Error> {
    //     todo!()
    // }

    fn get_signer(&mut self, reply_to: ReplyTo<AccountId>) -> Result<(), Error> {
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
        let result = self.chain.module_version(&port_id);

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

    fn query_compatible_versions(&self, reply_to: ReplyTo<Vec<String>>) -> Result<(), Error> {
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

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
        reply_to: ReplyTo<(Vec<PacketAckCommitment>, Height)>,
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
}
