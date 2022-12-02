use alloc::sync::Arc;
use std::thread;

use crossbeam_channel as channel;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::{error, Span};

use ibc_relayer_types::{
    core::{
        ics02_client::events::UpdateClient,
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
    proofs::Proofs,
    signer::Signer,
    Height,
};

use crate::{
    account::Balance,
    chain::requests::QueryPacketEventDataRequest,
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::ChainConfig,
    connection::ConnectionMsgType,
    consensus_state::{AnyConsensusState, AnyConsensusStateWithHeight},
    denom::DenomTrace,
    error::Error,
    event::IbcEventWithHeight,
    keyring::KeyEntry,
    light_client::AnyHeader,
    misbehaviour::MisbehaviourEvidence,
};

use super::{
    client::ClientSettings,
    endpoint::{ChainEndpoint, ChainStatus, HealthCheck},
    handle::{ChainHandle, ChainRequest, ReplyTo, Subscription},
    requests::*,
    tracking::TrackedMsgs,
};

pub struct Threads {
    pub chain_runtime: thread::JoinHandle<()>,
    pub event_monitor: Option<thread::JoinHandle<()>>,
}

pub struct ChainRuntime<Endpoint: ChainEndpoint> {
    /// The specific chain this runtime runs against
    chain: Endpoint,

    /// The sender side of a channel to this runtime. Any `ChainHandle` can use this to send
    /// chain requests to this runtime
    request_sender: channel::Sender<(Span, ChainRequest)>,

    /// The receiving side of a channel to this runtime. The runtime consumes chain requests coming
    /// in through this channel.
    request_receiver: channel::Receiver<(Span, ChainRequest)>,

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
        let (request_sender, request_receiver) = channel::unbounded();

        Self {
            rt,
            chain,
            request_sender,
            request_receiver,
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
                recv(self.request_receiver) -> event => {
                    let (span, event) = match event {
                        Ok((span, event)) => (span, event),
                        Err(e) => {
                            error!("received error via chain request channel: {}", e);
                            continue;
                        }
                    };

                    let _span = span.entered();

                    match event {
                        ChainRequest::Shutdown { reply_to } => {
                            let res = self.chain.shutdown();

                            reply_to.send(res)
                                .map_err(Error::send)?;

                            break;
                        },

                        ChainRequest::HealthCheck { reply_to } => {
                            self.health_check(reply_to)?
                        },

                        ChainRequest::Subscribe { reply_to } => {
                            self.subscribe(reply_to)?
                        },

                        ChainRequest::SendMessagesAndWaitCommit { tracked_msgs, reply_to } => {
                            self.send_messages_and_wait_commit(tracked_msgs, reply_to)?
                        },

                        ChainRequest::SendMessagesAndWaitCheckTx { tracked_msgs, reply_to } => {
                            self.send_messages_and_wait_check_tx(tracked_msgs, reply_to)?
                        },

                        ChainRequest::Signer { reply_to } => {
                            self.get_signer(reply_to)?
                        },

                        ChainRequest::Config { reply_to } => {
                            self.get_config(reply_to)?
                        },

                        ChainRequest::GetKey { reply_to } => {
                            self.get_key(reply_to)?
                        },

                        ChainRequest::AddKey { key_name, key, reply_to } => {
                            self.add_key(key_name, key, reply_to)?
                        },

                        ChainRequest::IbcVersion { reply_to } => {
                            self.ibc_version(reply_to)?
                        },

                        ChainRequest::BuildHeader { trusted_height, target_height, client_state, reply_to } => {
                            self.build_header(trusted_height, target_height, client_state, reply_to)?
                        },

                        ChainRequest::BuildClientState { height, settings, reply_to } => {
                            self.build_client_state(height, settings, reply_to)?
                        },

                        ChainRequest::BuildConsensusState { trusted, target, client_state, reply_to } => {
                            self.build_consensus_state(trusted, target, client_state, reply_to)?
                        },

                        ChainRequest::BuildMisbehaviour { client_state, update_event, reply_to } => {
                            self.check_misbehaviour(update_event, client_state, reply_to)?
                        },

                        ChainRequest::BuildConnectionProofsAndClientState { message_type, connection_id, client_id, height, reply_to } => {
                            self.build_connection_proofs_and_client_state(message_type, connection_id, client_id, height, reply_to)?
                        },

                        ChainRequest::BuildChannelProofs { port_id, channel_id, height, reply_to } => {
                            self.build_channel_proofs(port_id, channel_id, height, reply_to)?
                        },

                        ChainRequest::QueryBalance { key_name, denom, reply_to } => {
                            self.query_balance(key_name, denom, reply_to)?
                        },

                        ChainRequest::QueryAllBalances { key_name, reply_to } => {
                            self.query_all_balances(key_name, reply_to)?
                        },

                        ChainRequest::QueryDenomTrace { hash, reply_to } => {
                            self.query_denom_trace(hash, reply_to)?
                        },

                        ChainRequest::QueryApplicationStatus { reply_to } => {
                            self.query_application_status(reply_to)?
                        },

                        ChainRequest::QueryClients { request, reply_to } => {
                            self.query_clients(request, reply_to)?
                        },

                        ChainRequest::QueryClientConnections { request, reply_to } => {
                            self.query_client_connections(request, reply_to)?
                        },

                        ChainRequest::QueryClientState { request, include_proof, reply_to } => {
                            self.query_client_state(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryConsensusStates { request, reply_to } => {
                            self.query_consensus_states(request, reply_to)?
                        },

                        ChainRequest::QueryConsensusState { request, include_proof, reply_to } => {
                            self.query_consensus_state(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryUpgradedClientState { request, reply_to } => {
                            self.query_upgraded_client_state(request, reply_to)?
                        },

                        ChainRequest::QueryUpgradedConsensusState { request, reply_to } => {
                            self.query_upgraded_consensus_state(request, reply_to)?
                        },

                        ChainRequest::QueryCommitmentPrefix { reply_to } => {
                            self.query_commitment_prefix(reply_to)?
                        },

                        ChainRequest::QueryCompatibleVersions { reply_to } => {
                            self.query_compatible_versions(reply_to)?
                        },

                        ChainRequest::QueryConnection { request, include_proof, reply_to } => {
                            self.query_connection(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryConnections { request, reply_to } => {
                            self.query_connections(request, reply_to)?
                        },

                        ChainRequest::QueryConnectionChannels { request, reply_to } => {
                            self.query_connection_channels(request, reply_to)?
                        },

                        ChainRequest::QueryChannels { request, reply_to } => {
                            self.query_channels(request, reply_to)?
                        },

                        ChainRequest::QueryChannel { request, include_proof, reply_to } => {
                            self.query_channel(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryChannelClientState { request, reply_to } => {
                            self.query_channel_client_state(request, reply_to)?
                        },

                        ChainRequest::BuildPacketProofs { packet_type, port_id, channel_id, sequence, height, reply_to } => {
                            self.build_packet_proofs(packet_type, port_id, channel_id, sequence, height, reply_to)?
                        },

                        ChainRequest::QueryPacketCommitment { request, include_proof, reply_to } => {
                            self.query_packet_commitment(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryPacketCommitments { request, reply_to } => {
                            self.query_packet_commitments(request, reply_to)?
                        },

                        ChainRequest::QueryPacketReceipt { request, include_proof, reply_to } => {
                            self.query_packet_receipt(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryUnreceivedPackets { request, reply_to } => {
                            self.query_unreceived_packets(request, reply_to)?
                        },

                        ChainRequest::QueryPacketAcknowledgement { request, include_proof, reply_to } => {
                            self.query_packet_acknowledgement(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryPacketAcknowledgements { request, reply_to } => {
                            self.query_packet_acknowledgements(request, reply_to)?
                        },

                        ChainRequest::QueryUnreceivedAcknowledgement { request, reply_to } => {
                            self.query_unreceived_acknowledgement(request, reply_to)?
                        },

                        ChainRequest::QueryNextSequenceReceive { request, include_proof, reply_to } => {
                            self.query_next_sequence_receive(request, include_proof, reply_to)?
                        },

                        ChainRequest::QueryPacketEventDataFromTxs { request, reply_to } => {
                            self.query_txs(request, reply_to)?
                        },

                        ChainRequest::QueryPacketEventData { request, reply_to } => {
                            self.query_packet_events(request, reply_to)?
                        },

                        ChainRequest::QueryHostConsensusState { request, reply_to } => {
                            self.query_host_consensus_state(request, reply_to)?
                        },

                        ChainRequest::MaybeRegisterCounterpartyPayee { channel_id, port_id, counterparty_payee, reply_to } => {
                            self.maybe_register_counterparty_payee(&channel_id, &port_id, &counterparty_payee, reply_to)?
                        }
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
        let subscription = self.chain.subscribe();
        reply_to.send(subscription).map_err(Error::send)
    }

    fn send_messages_and_wait_commit(
        &mut self,
        tracked_msgs: TrackedMsgs,
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
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
        denom: Option<String>,
        reply_to: ReplyTo<Balance>,
    ) -> Result<(), Error> {
        let balance = self
            .chain
            .query_balance(key_name.as_deref(), denom.as_deref());

        reply_to.send(balance).map_err(Error::send)
    }

    fn query_all_balances(
        &self,
        key_name: Option<String>,
        reply_to: ReplyTo<Vec<Balance>>,
    ) -> Result<(), Error> {
        let balances = self.chain.query_all_balances(key_name.as_deref());
        reply_to.send(balances).map_err(Error::send)
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
        let result = Ok(self.chain.config().clone());
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
                let header = header.into();
                let support = support.into_iter().map(|h| h.into()).collect();
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
            .map(|cs| cs.into());

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
            .map(|cs| cs.into());

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
        let res = self.chain.query_client_state(request, include_proof);

        reply_to.send(res).map_err(Error::send)
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
        reply_to: ReplyTo<(AnyClientState, MerkleProof)>,
    ) -> Result<(), Error> {
        let result = self.chain.query_upgraded_client_state(request);

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
        let result = self.chain.query_upgraded_consensus_state(request);

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
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_txs(request);
        reply_to.send(result).map_err(Error::send)
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
        reply_to: ReplyTo<Vec<IbcEventWithHeight>>,
    ) -> Result<(), Error> {
        let result = self.chain.query_packet_events(request);

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
            .map(|h| h.into());

        reply_to.send(result).map_err(Error::send)?;

        Ok(())
    }

    fn maybe_register_counterparty_payee(
        &mut self,
        channel_id: &ChannelId,
        port_id: &PortId,
        counterparty_payee: &Signer,
        reply_to: ReplyTo<()>,
    ) -> Result<(), Error> {
        let result =
            self.chain
                .maybe_register_counterparty_payee(channel_id, port_id, counterparty_payee);

        reply_to.send(result).map_err(Error::send)?;

        Ok(())
    }
}
