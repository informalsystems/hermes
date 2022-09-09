//! Implementation of a global context mock. Used in testing handlers of all IBC modules.

use crate::prelude::*;

use alloc::collections::btree_map::BTreeMap;
use alloc::sync::Arc;
use core::borrow::Borrow;
use core::cmp::min;
use core::fmt::{Debug, Formatter};
use core::ops::{Add, Sub};
use core::time::Duration;
use std::sync::Mutex;

use ibc_proto::google::protobuf::Any;
use sha2::Digest;
use tracing::debug;

use crate::clients::ics07_tendermint::client_state::test_util::get_dummy_tendermint_client_state;
use crate::clients::ics07_tendermint::client_state::ClientState as TmClientState;
use crate::core::ics02_client::client_state::ClientState;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::context::{ClientKeeper, ClientReader};
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics02_client::header::Header;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::core::ics03_connection::error::Error as Ics03Error;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::core::ics04_channel::error::Error as Ics04Error;
use crate::core::ics04_channel::packet::{Receipt, Sequence};
use crate::core::ics05_port::context::PortReader;
use crate::core::ics05_port::error::Error as Ics05Error;
use crate::core::ics05_port::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentPrefix;
use crate::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics26_routing::context::{Ics26Context, Module, ModuleId, Router, RouterBuilder};
use crate::core::ics26_routing::handler::{deliver, dispatch, MsgReceipt};
use crate::core::ics26_routing::msgs::Ics26Envelope;
use crate::events::IbcEvent;
use crate::mock::client_state::{MockClientRecord, MockClientState};
use crate::mock::consensus_state::MockConsensusState;
use crate::mock::header::MockHeader;
use crate::mock::host::{HostBlock, HostType};
use crate::relayer::ics18_relayer::context::Ics18Context;
use crate::relayer::ics18_relayer::error::Error as Ics18Error;
use crate::signer::Signer;
use crate::timestamp::Timestamp;
use crate::Height;

pub const DEFAULT_BLOCK_TIME_SECS: u64 = 3;

/// A context implementing the dependencies necessary for testing any IBC module.
#[derive(Debug)]
pub struct MockContext {
    /// The type of host chain underlying this mock context.
    host_chain_type: HostType,

    /// Host chain identifier.
    host_chain_id: ChainId,

    /// Maximum size for the history of the host chain. Any block older than this is pruned.
    max_history_size: usize,

    /// The chain of blocks underlying this context. A vector of size up to `max_history_size`
    /// blocks, ascending order by their height (latest block is on the last position).
    history: Vec<HostBlock>,

    /// Average time duration between blocks
    block_time: Duration,

    /// An object that stores all IBC related data.
    pub ibc_store: Arc<Mutex<MockIbcStore>>,

    /// ICS26 router impl
    router: MockRouter,
}

/// Returns a MockContext with bare minimum initialization: no clients, no connections and no channels are
/// present, and the chain has Height(5). This should be used sparingly, mostly for testing the
/// creation of new domain objects.
impl Default for MockContext {
    fn default() -> Self {
        Self::new(
            ChainId::new("mockgaia".to_string(), 0),
            HostType::Mock,
            5,
            Height::new(0, 5).unwrap(),
        )
    }
}

/// A manual clone impl is provided because the tests are oblivious to the fact that the `ibc_store`
/// is a shared ptr.
impl Clone for MockContext {
    fn clone(&self) -> Self {
        let ibc_store = {
            let ibc_store = self.ibc_store.lock().unwrap().clone();
            Arc::new(Mutex::new(ibc_store))
        };
        Self {
            host_chain_type: self.host_chain_type,
            host_chain_id: self.host_chain_id.clone(),
            max_history_size: self.max_history_size,
            history: self.history.clone(),
            block_time: self.block_time,
            ibc_store,
            router: self.router.clone(),
        }
    }
}

/// Implementation of internal interface for use in testing. The methods in this interface should
/// _not_ be accessible to any Ics handler.
impl MockContext {
    /// Creates a mock context. Parameter `max_history_size` determines how many blocks will
    /// the chain maintain in its history, which also determines the pruning window. Parameter
    /// `latest_height` determines the current height of the chain. This context
    /// has support to emulate two type of underlying chains: Mock or SyntheticTendermint.
    pub fn new(
        host_id: ChainId,
        host_type: HostType,
        max_history_size: usize,
        latest_height: Height,
    ) -> Self {
        assert_ne!(
            max_history_size, 0,
            "The chain must have a non-zero max_history_size"
        );

        assert_ne!(
            latest_height.revision_height(),
            0,
            "The chain must have a non-zero revision_height"
        );

        // Compute the number of blocks to store.
        let n = min(max_history_size as u64, latest_height.revision_height());

        assert_eq!(
            host_id.version(),
            latest_height.revision_number(),
            "The version in the chain identifier must match the version in the latest height"
        );

        let block_time = Duration::from_secs(DEFAULT_BLOCK_TIME_SECS);
        let next_block_timestamp = Timestamp::now().add(block_time).unwrap();
        MockContext {
            host_chain_type: host_type,
            host_chain_id: host_id.clone(),
            max_history_size,
            history: (0..n)
                .rev()
                .map(|i| {
                    // generate blocks with timestamps -> N, N - BT, N - 2BT, ...
                    // where N = now(), BT = block_time
                    HostBlock::generate_block(
                        host_id.clone(),
                        host_type,
                        latest_height.sub(i).unwrap().revision_height(),
                        next_block_timestamp
                            .sub(Duration::from_secs(DEFAULT_BLOCK_TIME_SECS * (i + 1)))
                            .unwrap(),
                    )
                })
                .collect(),
            block_time,
            ibc_store: Arc::new(Mutex::new(MockIbcStore::default())),
            router: Default::default(),
        }
    }

    /// Associates a client record to this context.
    /// Given a client id and a height, registers a new client in the context and also associates
    /// to this client a mock client state and a mock consensus state for height `height`. The type
    /// of this client is implicitly assumed to be Mock.
    pub fn with_client(self, client_id: &ClientId, height: Height) -> Self {
        self.with_client_parametrized(client_id, height, Some(ClientType::Mock), Some(height))
    }

    /// Similar to `with_client`, this function associates a client record to this context, but
    /// additionally permits to parametrize two details of the client. If `client_type` is None,
    /// then the client will have type Mock, otherwise the specified type. If
    /// `consensus_state_height` is None, then the client will be initialized with a consensus
    /// state matching the same height as the client state (`client_state_height`).
    pub fn with_client_parametrized(
        self,
        client_id: &ClientId,
        client_state_height: Height,
        client_type: Option<ClientType>,
        consensus_state_height: Option<Height>,
    ) -> Self {
        let cs_height = consensus_state_height.unwrap_or(client_state_height);

        let client_type = client_type.unwrap_or(ClientType::Mock);
        let (client_state, consensus_state) = match client_type {
            // If it's a mock client, create the corresponding mock states.
            ClientType::Mock => (
                Some(MockClientState::new(MockHeader::new(client_state_height)).into_box()),
                MockConsensusState::new(MockHeader::new(cs_height)).into_box(),
            ),
            // If it's a Tendermint client, we need TM states.
            ClientType::Tendermint => {
                let light_block = HostBlock::generate_tm_block(
                    self.host_chain_id.clone(),
                    cs_height.revision_height(),
                    Timestamp::now(),
                );

                let client_state =
                    get_dummy_tendermint_client_state(light_block.header().clone()).into_box();

                // Return the tuple.
                (Some(client_state), light_block.into())
            }
        };
        let consensus_states = vec![(cs_height, consensus_state)].into_iter().collect();

        debug!("consensus states: {:?}", consensus_states);

        let client_record = MockClientRecord {
            client_type,
            client_state,
            consensus_states,
        };
        self.ibc_store
            .lock()
            .unwrap()
            .clients
            .insert(client_id.clone(), client_record);
        self
    }

    pub fn with_client_parametrized_history(
        self,
        client_id: &ClientId,
        client_state_height: Height,
        client_type: Option<ClientType>,
        consensus_state_height: Option<Height>,
    ) -> Self {
        let cs_height = consensus_state_height.unwrap_or(client_state_height);
        let prev_cs_height = cs_height.clone().sub(1).unwrap_or(client_state_height);

        let client_type = client_type.unwrap_or(ClientType::Mock);
        let now = Timestamp::now();

        let (client_state, consensus_state) = match client_type {
            // If it's a mock client, create the corresponding mock states.
            ClientType::Mock => (
                Some(MockClientState::new(MockHeader::new(client_state_height)).into_box()),
                MockConsensusState::new(MockHeader::new(cs_height)).into_box(),
            ),
            // If it's a Tendermint client, we need TM states.
            ClientType::Tendermint => {
                let light_block = HostBlock::generate_tm_block(
                    self.host_chain_id.clone(),
                    cs_height.revision_height(),
                    now,
                );

                let client_state =
                    get_dummy_tendermint_client_state(light_block.header().clone()).into_box();

                // Return the tuple.
                (Some(client_state), light_block.into())
            }
        };

        let prev_consensus_state = match client_type {
            // If it's a mock client, create the corresponding mock states.
            ClientType::Mock => MockConsensusState::new(MockHeader::new(prev_cs_height)).into_box(),
            // If it's a Tendermint client, we need TM states.
            ClientType::Tendermint => {
                let light_block = HostBlock::generate_tm_block(
                    self.host_chain_id.clone(),
                    prev_cs_height.revision_height(),
                    now.sub(self.block_time).unwrap(),
                );
                light_block.into()
            }
        };

        let consensus_states = vec![
            (prev_cs_height, prev_consensus_state),
            (cs_height, consensus_state),
        ]
        .into_iter()
        .collect();

        debug!("consensus states: {:?}", consensus_states);

        let client_record = MockClientRecord {
            client_type,
            client_state,
            consensus_states,
        };

        self.ibc_store
            .lock()
            .unwrap()
            .clients
            .insert(client_id.clone(), client_record);
        self
    }

    /// Associates a connection to this context.
    pub fn with_connection(
        self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Self {
        self.ibc_store
            .lock()
            .unwrap()
            .connections
            .insert(connection_id, connection_end);
        self
    }

    /// Associates a channel (in an arbitrary state) to this context.
    pub fn with_channel(
        self,
        port_id: PortId,
        chan_id: ChannelId,
        channel_end: ChannelEnd,
    ) -> Self {
        let mut channels = self.ibc_store.lock().unwrap().channels.clone();
        channels
            .entry(port_id)
            .or_default()
            .insert(chan_id, channel_end);
        self.ibc_store.lock().unwrap().channels = channels;
        self
    }

    pub fn with_send_sequence(
        self,
        port_id: PortId,
        chan_id: ChannelId,
        seq_number: Sequence,
    ) -> Self {
        let mut next_sequence_send = self.ibc_store.lock().unwrap().next_sequence_send.clone();
        next_sequence_send
            .entry(port_id)
            .or_default()
            .insert(chan_id, seq_number);
        self.ibc_store.lock().unwrap().next_sequence_send = next_sequence_send;
        self
    }

    pub fn with_recv_sequence(
        self,
        port_id: PortId,
        chan_id: ChannelId,
        seq_number: Sequence,
    ) -> Self {
        let mut next_sequence_recv = self.ibc_store.lock().unwrap().next_sequence_recv.clone();
        next_sequence_recv
            .entry(port_id)
            .or_default()
            .insert(chan_id, seq_number);
        self.ibc_store.lock().unwrap().next_sequence_recv = next_sequence_recv;
        self
    }

    pub fn with_ack_sequence(
        self,
        port_id: PortId,
        chan_id: ChannelId,
        seq_number: Sequence,
    ) -> Self {
        let mut next_sequence_ack = self.ibc_store.lock().unwrap().next_sequence_send.clone();
        next_sequence_ack
            .entry(port_id)
            .or_default()
            .insert(chan_id, seq_number);
        self.ibc_store.lock().unwrap().next_sequence_ack = next_sequence_ack;
        self
    }

    pub fn with_height(self, target_height: Height) -> Self {
        let latest_height = self.latest_height();
        if target_height.revision_number() > latest_height.revision_number() {
            unimplemented!()
        } else if target_height.revision_number() < latest_height.revision_number() {
            panic!("Cannot rewind history of the chain to a smaller revision number!")
        } else if target_height.revision_height() < latest_height.revision_height() {
            panic!("Cannot rewind history of the chain to a smaller revision height!")
        } else if target_height.revision_height() > latest_height.revision_height() {
            // Repeatedly advance the host chain height till we hit the desired height
            let mut ctx = MockContext { ..self };
            while ctx.latest_height().revision_height() < target_height.revision_height() {
                ctx.advance_host_chain_height()
            }
            ctx
        } else {
            // Both the revision number and height match
            self
        }
    }

    pub fn with_packet_commitment(
        self,
        port_id: PortId,
        chan_id: ChannelId,
        seq: Sequence,
        data: PacketCommitment,
    ) -> Self {
        let mut packet_commitment = self.ibc_store.lock().unwrap().packet_commitment.clone();
        packet_commitment
            .entry(port_id)
            .or_default()
            .entry(chan_id)
            .or_default()
            .insert(seq, data);
        self.ibc_store.lock().unwrap().packet_commitment = packet_commitment;
        self
    }

    pub fn with_router(self, router: MockRouter) -> Self {
        Self { router, ..self }
    }

    /// Accessor for a block of the local (host) chain from this context.
    /// Returns `None` if the block at the requested height does not exist.
    pub fn host_block(&self, target_height: Height) -> Option<&HostBlock> {
        let target = target_height.revision_height() as usize;
        let latest = self.latest_height().revision_height() as usize;

        // Check that the block is not too advanced, nor has it been pruned.
        if (target > latest) || (target <= latest - self.history.len()) {
            None // Block for requested height does not exist in history.
        } else {
            Some(&self.history[self.history.len() + target - latest - 1])
        }
    }

    /// Triggers the advancing of the host chain, by extending the history of blocks (or headers).
    pub fn advance_host_chain_height(&mut self) {
        let latest_block = self.history.last().expect("history cannot be empty");
        let new_block = HostBlock::generate_block(
            self.host_chain_id.clone(),
            self.host_chain_type,
            latest_block.height().increment().revision_height(),
            latest_block.timestamp().add(self.block_time).unwrap(),
        );

        // Append the new header at the tip of the history.
        if self.history.len() >= self.max_history_size {
            // History is full, we rotate and replace the tip with the new header.
            self.history.rotate_left(1);
            self.history[self.max_history_size - 1] = new_block;
        } else {
            // History is not full yet.
            self.history.push(new_block);
        }
    }

    /// A datagram passes from the relayer to the IBC module (on host chain).
    /// Alternative method to `Ics18Context::send` that does not exercise any serialization.
    /// Used in testing the Ics18 algorithms, hence this may return a Ics18Error.
    pub fn deliver(&mut self, msg: Ics26Envelope) -> Result<(), Ics18Error> {
        dispatch(self, msg).map_err(Ics18Error::transaction_failed)?;
        // Create a new block.
        self.advance_host_chain_height();
        Ok(())
    }

    /// Validates this context. Should be called after the context is mutated by a test.
    pub fn validate(&self) -> Result<(), String> {
        // Check that the number of entries is not higher than window size.
        if self.history.len() > self.max_history_size {
            return Err("too many entries".to_string());
        }

        // Check the content of the history.
        if !self.history.is_empty() {
            // Get the highest block.
            let lh = &self.history[self.history.len() - 1];
            // Check latest is properly updated with highest header height.
            if lh.height() != self.latest_height() {
                return Err("latest height is not updated".to_string());
            }
        }

        // Check that headers in the history are in sequential order.
        for i in 1..self.history.len() {
            let ph = &self.history[i - 1];
            let h = &self.history[i];
            if ph.height().increment() != h.height() {
                return Err("headers in history not sequential".to_string());
            }
        }
        Ok(())
    }

    pub fn add_port(&mut self, port_id: PortId) {
        let module_id = ModuleId::new(format!("module{}", port_id).into()).unwrap();
        self.ibc_store
            .lock()
            .unwrap()
            .port_to_module
            .insert(port_id, module_id);
    }

    pub fn scope_port_to_module(&mut self, port_id: PortId, module_id: ModuleId) {
        self.ibc_store
            .lock()
            .unwrap()
            .port_to_module
            .insert(port_id, module_id);
    }

    pub fn latest_client_states(&self, client_id: &ClientId) -> Box<dyn ClientState> {
        self.ibc_store.lock().unwrap().clients[client_id]
            .client_state
            .as_ref()
            .unwrap()
            .clone()
    }

    pub fn latest_consensus_states(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Box<dyn ConsensusState> {
        dyn_clone::clone_box(
            self.ibc_store.lock().unwrap().clients[client_id]
                .consensus_states
                .get(height)
                .unwrap()
                .as_ref(),
        )
    }

    #[inline]
    fn latest_height(&self) -> Height {
        self.history
            .last()
            .expect("history cannot be empty")
            .height()
    }

    pub fn ibc_store_share(&self) -> Arc<Mutex<MockIbcStore>> {
        self.ibc_store.clone()
    }
}

type PortChannelIdMap<V> = BTreeMap<PortId, BTreeMap<ChannelId, V>>;

/// An object that stores all IBC related data.
#[derive(Clone, Debug, Default)]
pub struct MockIbcStore {
    /// The set of all clients, indexed by their id.
    pub clients: BTreeMap<ClientId, MockClientRecord>,

    /// Tracks the processed time for clients header updates
    pub client_processed_times: BTreeMap<(ClientId, Height), Timestamp>,

    /// Tracks the processed height for the clients
    pub client_processed_heights: BTreeMap<(ClientId, Height), Height>,

    /// Counter for the client identifiers, necessary for `increase_client_counter` and the
    /// `client_counter` methods.
    pub client_ids_counter: u64,

    /// Association between client ids and connection ids.
    pub client_connections: BTreeMap<ClientId, ConnectionId>,

    /// All the connections in the store.
    pub connections: BTreeMap<ConnectionId, ConnectionEnd>,

    /// Counter for connection identifiers (see `increase_connection_counter`).
    pub connection_ids_counter: u64,

    /// Association between connection ids and channel ids.
    pub connection_channels: BTreeMap<ConnectionId, Vec<(PortId, ChannelId)>>,

    /// Counter for channel identifiers (see `increase_channel_counter`).
    pub channel_ids_counter: u64,

    /// All the channels in the store. TODO Make new key PortId X ChanneId
    pub channels: PortChannelIdMap<ChannelEnd>,

    /// Tracks the sequence number for the next packet to be sent.
    pub next_sequence_send: PortChannelIdMap<Sequence>,

    /// Tracks the sequence number for the next packet to be received.
    pub next_sequence_recv: PortChannelIdMap<Sequence>,

    /// Tracks the sequence number for the next packet to be acknowledged.
    pub next_sequence_ack: PortChannelIdMap<Sequence>,

    pub packet_acknowledgement: PortChannelIdMap<BTreeMap<Sequence, AcknowledgementCommitment>>,

    /// Maps ports to the the module that owns it
    pub port_to_module: BTreeMap<PortId, ModuleId>,

    /// Constant-size commitments to packets data fields
    pub packet_commitment: PortChannelIdMap<BTreeMap<Sequence, PacketCommitment>>,

    // Used by unordered channel
    pub packet_receipt: PortChannelIdMap<BTreeMap<Sequence, Receipt>>,
}

#[derive(Default)]
pub struct MockRouterBuilder(MockRouter);

impl RouterBuilder for MockRouterBuilder {
    type Router = MockRouter;

    fn add_route(mut self, module_id: ModuleId, module: impl Module) -> Result<Self, String> {
        match self.0 .0.insert(module_id, Arc::new(module)) {
            None => Ok(self),
            Some(_) => Err("Duplicate module_id".to_owned()),
        }
    }

    fn build(self) -> Self::Router {
        self.0
    }
}

#[derive(Clone, Default)]
pub struct MockRouter(BTreeMap<ModuleId, Arc<dyn Module>>);

impl Debug for MockRouter {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.0.keys().collect::<Vec<&ModuleId>>())
    }
}

impl Router for MockRouter {
    fn get_route_mut(&mut self, module_id: &impl Borrow<ModuleId>) -> Option<&mut dyn Module> {
        self.0.get_mut(module_id.borrow()).and_then(Arc::get_mut)
    }

    fn has_route(&self, module_id: &impl Borrow<ModuleId>) -> bool {
        self.0.get(module_id.borrow()).is_some()
    }
}

impl Ics26Context for MockContext {
    type Router = MockRouter;

    fn router(&self) -> &Self::Router {
        &self.router
    }

    fn router_mut(&mut self) -> &mut Self::Router {
        &mut self.router
    }
}

impl PortReader for MockContext {
    fn lookup_module_by_port(&self, port_id: &PortId) -> Result<ModuleId, Error> {
        match self.ibc_store.lock().unwrap().port_to_module.get(port_id) {
            Some(mod_id) => Ok(mod_id.clone()),
            None => Err(Ics05Error::unknown_port(port_id.clone())),
        }
    }
}

impl ChannelReader for MockContext {
    fn channel_end(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<ChannelEnd, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .channels
            .get(port_id)
            .and_then(|map| map.get(channel_id))
        {
            Some(channel_end) => Ok(channel_end.clone()),
            None => Err(Ics04Error::channel_not_found(
                port_id.clone(),
                channel_id.clone(),
            )),
        }
    }

    fn connection_end(&self, cid: &ConnectionId) -> Result<ConnectionEnd, Ics04Error> {
        ConnectionReader::connection_end(self, cid).map_err(Ics04Error::ics03_connection)
    }

    fn connection_channels(
        &self,
        cid: &ConnectionId,
    ) -> Result<Vec<(PortId, ChannelId)>, Ics04Error> {
        match self.ibc_store.lock().unwrap().connection_channels.get(cid) {
            Some(pcid) => Ok(pcid.clone()),
            None => Err(Ics04Error::missing_channel()),
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, Ics04Error> {
        ClientReader::client_state(self, client_id)
            .map_err(|e| Ics04Error::ics03_connection(Ics03Error::ics02_client(e)))
    }

    fn client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Box<dyn ConsensusState>, Ics04Error> {
        ClientReader::consensus_state(self, client_id, height)
            .map_err(|e| Ics04Error::ics03_connection(Ics03Error::ics02_client(e)))
    }

    fn get_next_sequence_send(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Sequence, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .next_sequence_send
            .get(port_id)
            .and_then(|map| map.get(channel_id))
        {
            Some(sequence) => Ok(*sequence),
            None => Err(Ics04Error::missing_next_send_seq(
                port_id.clone(),
                channel_id.clone(),
            )),
        }
    }

    fn get_next_sequence_recv(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Sequence, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .next_sequence_recv
            .get(port_id)
            .and_then(|map| map.get(channel_id))
        {
            Some(sequence) => Ok(*sequence),
            None => Err(Ics04Error::missing_next_recv_seq(
                port_id.clone(),
                channel_id.clone(),
            )),
        }
    }

    fn get_next_sequence_ack(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Sequence, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .next_sequence_ack
            .get(port_id)
            .and_then(|map| map.get(channel_id))
        {
            Some(sequence) => Ok(*sequence),
            None => Err(Ics04Error::missing_next_ack_seq(
                port_id.clone(),
                channel_id.clone(),
            )),
        }
    }

    fn get_packet_commitment(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        seq: Sequence,
    ) -> Result<PacketCommitment, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .packet_commitment
            .get(port_id)
            .and_then(|map| map.get(channel_id))
            .and_then(|map| map.get(&seq))
        {
            Some(commitment) => Ok(commitment.clone()),
            None => Err(Ics04Error::packet_commitment_not_found(seq)),
        }
    }

    fn get_packet_receipt(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        seq: Sequence,
    ) -> Result<Receipt, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .packet_receipt
            .get(port_id)
            .and_then(|map| map.get(channel_id))
            .and_then(|map| map.get(&seq))
        {
            Some(receipt) => Ok(receipt.clone()),
            None => Err(Ics04Error::packet_receipt_not_found(seq)),
        }
    }

    fn get_packet_acknowledgement(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        seq: Sequence,
    ) -> Result<AcknowledgementCommitment, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .packet_acknowledgement
            .get(port_id)
            .and_then(|map| map.get(channel_id))
            .and_then(|map| map.get(&seq))
        {
            Some(ack) => Ok(ack.clone()),
            None => Err(Ics04Error::packet_acknowledgement_not_found(seq)),
        }
    }

    fn hash(&self, value: Vec<u8>) -> Vec<u8> {
        sha2::Sha256::digest(value).to_vec()
    }

    fn host_height(&self) -> Height {
        self.latest_height()
    }

    fn host_timestamp(&self) -> Timestamp {
        ClientReader::host_timestamp(self)
    }

    fn host_consensus_state(&self, height: Height) -> Result<Box<dyn ConsensusState>, Ics04Error> {
        ConnectionReader::host_consensus_state(self, height).map_err(Ics04Error::ics03_connection)
    }

    fn pending_host_consensus_state(&self) -> Result<Box<dyn ConsensusState>, Ics04Error> {
        ClientReader::pending_host_consensus_state(self)
            .map_err(|e| Ics04Error::ics03_connection(Ics03Error::ics02_client(e)))
    }

    fn client_update_time(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Timestamp, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .client_processed_times
            .get(&(client_id.clone(), height))
        {
            Some(time) => Ok(*time),
            None => Err(Ics04Error::processed_time_not_found(
                client_id.clone(),
                height,
            )),
        }
    }

    fn client_update_height(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Height, Ics04Error> {
        match self
            .ibc_store
            .lock()
            .unwrap()
            .client_processed_heights
            .get(&(client_id.clone(), height))
        {
            Some(height) => Ok(*height),
            None => Err(Ics04Error::processed_height_not_found(
                client_id.clone(),
                height,
            )),
        }
    }

    fn channel_counter(&self) -> Result<u64, Ics04Error> {
        Ok(self.ibc_store.lock().unwrap().channel_ids_counter)
    }

    fn max_expected_time_per_block(&self) -> Duration {
        self.block_time
    }
}

impl ChannelKeeper for MockContext {
    fn store_packet_commitment(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .packet_commitment
            .entry(port_id)
            .or_default()
            .entry(channel_id)
            .or_default()
            .insert(seq, commitment);
        Ok(())
    }

    fn store_packet_acknowledgement(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
        ack_commitment: AcknowledgementCommitment,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .packet_acknowledgement
            .entry(port_id)
            .or_default()
            .entry(channel_id)
            .or_default()
            .insert(seq, ack_commitment);
        Ok(())
    }

    fn delete_packet_acknowledgement(
        &mut self,
        port_id: &PortId,
        channel_id: &ChannelId,
        seq: Sequence,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .packet_acknowledgement
            .get_mut(port_id)
            .and_then(|map| map.get_mut(channel_id))
            .and_then(|map| map.remove(&seq));
        Ok(())
    }

    fn store_connection_channels(
        &mut self,
        cid: ConnectionId,
        port_id: PortId,
        channel_id: ChannelId,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .connection_channels
            .entry(cid)
            .or_insert_with(Vec::new)
            .push((port_id, channel_id));
        Ok(())
    }

    fn store_channel(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        channel_end: ChannelEnd,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .channels
            .entry(port_id)
            .or_default()
            .insert(channel_id, channel_end);
        Ok(())
    }

    fn store_next_sequence_send(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .next_sequence_send
            .entry(port_id)
            .or_default()
            .insert(channel_id, seq);
        Ok(())
    }

    fn store_next_sequence_recv(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .next_sequence_recv
            .entry(port_id)
            .or_default()
            .insert(channel_id, seq);
        Ok(())
    }

    fn store_next_sequence_ack(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .next_sequence_ack
            .entry(port_id)
            .or_default()
            .insert(channel_id, seq);
        Ok(())
    }

    fn increase_channel_counter(&mut self) {
        self.ibc_store.lock().unwrap().channel_ids_counter += 1;
    }

    fn delete_packet_commitment(
        &mut self,
        port_id: &PortId,
        channel_id: &ChannelId,
        seq: Sequence,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .packet_commitment
            .get_mut(port_id)
            .and_then(|map| map.get_mut(channel_id))
            .and_then(|map| map.remove(&seq));
        Ok(())
    }

    fn store_packet_receipt(
        &mut self,
        port_id: PortId,
        channel_id: ChannelId,
        seq: Sequence,
        receipt: Receipt,
    ) -> Result<(), Ics04Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .packet_receipt
            .entry(port_id)
            .or_default()
            .entry(channel_id)
            .or_default()
            .insert(seq, receipt);
        Ok(())
    }
}

impl ConnectionReader for MockContext {
    fn connection_end(&self, cid: &ConnectionId) -> Result<ConnectionEnd, Ics03Error> {
        match self.ibc_store.lock().unwrap().connections.get(cid) {
            Some(connection_end) => Ok(connection_end.clone()),
            None => Err(Ics03Error::connection_not_found(cid.clone())),
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, Ics03Error> {
        // Forward method call to the Ics2 Client-specific method.
        ClientReader::client_state(self, client_id).map_err(Ics03Error::ics02_client)
    }

    fn decode_client_state(&self, client_state: Any) -> Result<Box<dyn ClientState>, Ics03Error> {
        ClientReader::decode_client_state(self, client_state).map_err(Ics03Error::ics02_client)
    }

    fn host_current_height(&self) -> Height {
        self.latest_height()
    }

    fn host_oldest_height(&self) -> Height {
        // history must be non-empty, so `self.history[0]` is valid
        self.history[0].height()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        CommitmentPrefix::try_from(b"mock".to_vec()).unwrap()
    }

    fn client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Box<dyn ConsensusState>, Ics03Error> {
        // Forward method call to the Ics2Client-specific method.
        self.consensus_state(client_id, height)
            .map_err(Ics03Error::ics02_client)
    }

    fn host_consensus_state(&self, height: Height) -> Result<Box<dyn ConsensusState>, Ics03Error> {
        ClientReader::host_consensus_state(self, height).map_err(Ics03Error::ics02_client)
    }

    fn connection_counter(&self) -> Result<u64, Ics03Error> {
        Ok(self.ibc_store.lock().unwrap().connection_ids_counter)
    }
}

impl ConnectionKeeper for MockContext {
    fn store_connection(
        &mut self,
        connection_id: ConnectionId,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Ics03Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .connections
            .insert(connection_id, connection_end.clone());
        Ok(())
    }

    fn store_connection_to_client(
        &mut self,
        connection_id: ConnectionId,
        client_id: &ClientId,
    ) -> Result<(), Ics03Error> {
        self.ibc_store
            .lock()
            .unwrap()
            .client_connections
            .insert(client_id.clone(), connection_id);
        Ok(())
    }

    fn increase_connection_counter(&mut self) {
        self.ibc_store.lock().unwrap().connection_ids_counter += 1;
    }
}

impl ClientReader for MockContext {
    fn client_type(&self, client_id: &ClientId) -> Result<ClientType, Ics02Error> {
        match self.ibc_store.lock().unwrap().clients.get(client_id) {
            Some(client_record) => Ok(client_record.client_type),
            None => Err(Ics02Error::client_not_found(client_id.clone())),
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, Ics02Error> {
        match self.ibc_store.lock().unwrap().clients.get(client_id) {
            Some(client_record) => client_record
                .client_state
                .clone()
                .ok_or_else(|| Ics02Error::client_not_found(client_id.clone())),
            None => Err(Ics02Error::client_not_found(client_id.clone())),
        }
    }

    fn decode_client_state(&self, client_state: Any) -> Result<Box<dyn ClientState>, Ics02Error> {
        if let Ok(client_state) = TmClientState::try_from(client_state.clone()) {
            Ok(client_state.into_box())
        } else if let Ok(client_state) = MockClientState::try_from(client_state.clone()) {
            Ok(client_state.into_box())
        } else {
            Err(Ics02Error::unknown_client_state_type(client_state.type_url))
        }
    }

    fn consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Box<dyn ConsensusState>, Ics02Error> {
        match self.ibc_store.lock().unwrap().clients.get(client_id) {
            Some(client_record) => match client_record.consensus_states.get(&height) {
                Some(consensus_state) => Ok(consensus_state.clone()),
                None => Err(Ics02Error::consensus_state_not_found(
                    client_id.clone(),
                    height,
                )),
            },
            None => Err(Ics02Error::consensus_state_not_found(
                client_id.clone(),
                height,
            )),
        }
    }

    /// Search for the lowest consensus state higher than `height`.
    fn next_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Ics02Error> {
        let ibc_store = self.ibc_store.lock().unwrap();
        let client_record = ibc_store
            .clients
            .get(client_id)
            .ok_or_else(|| Ics02Error::client_not_found(client_id.clone()))?;

        // Get the consensus state heights and sort them in ascending order.
        let mut heights: Vec<Height> = client_record.consensus_states.keys().cloned().collect();
        heights.sort();

        // Search for next state.
        for h in heights {
            if h > height {
                // unwrap should never happen, as the consensus state for h must exist
                return Ok(Some(
                    client_record.consensus_states.get(&h).unwrap().clone(),
                ));
            }
        }
        Ok(None)
    }

    /// Search for the highest consensus state lower than `height`.
    fn prev_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Option<Box<dyn ConsensusState>>, Ics02Error> {
        let ibc_store = self.ibc_store.lock().unwrap();
        let client_record = ibc_store
            .clients
            .get(client_id)
            .ok_or_else(|| Ics02Error::client_not_found(client_id.clone()))?;

        // Get the consensus state heights and sort them in descending order.
        let mut heights: Vec<Height> = client_record.consensus_states.keys().cloned().collect();
        heights.sort_by(|a, b| b.cmp(a));

        // Search for previous state.
        for h in heights {
            if h < height {
                // unwrap should never happen, as the consensus state for h must exist
                return Ok(Some(
                    client_record.consensus_states.get(&h).unwrap().clone(),
                ));
            }
        }
        Ok(None)
    }

    fn host_height(&self) -> Height {
        self.latest_height()
    }

    fn host_timestamp(&self) -> Timestamp {
        self.history
            .last()
            .expect("history cannot be empty")
            .timestamp()
            .add(self.block_time)
            .unwrap()
    }

    fn host_consensus_state(&self, height: Height) -> Result<Box<dyn ConsensusState>, Ics02Error> {
        match self.host_block(height) {
            Some(block_ref) => Ok(block_ref.clone().into()),
            None => Err(Ics02Error::missing_local_consensus_state(height)),
        }
    }

    fn pending_host_consensus_state(&self) -> Result<Box<dyn ConsensusState>, Ics02Error> {
        Err(Ics02Error::implementation_specific())
    }

    fn client_counter(&self) -> Result<u64, Ics02Error> {
        Ok(self.ibc_store.lock().unwrap().client_ids_counter)
    }
}

impl ClientKeeper for MockContext {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), Ics02Error> {
        let mut ibc_store = self.ibc_store.lock().unwrap();
        let client_record = ibc_store
            .clients
            .entry(client_id)
            .or_insert(MockClientRecord {
                client_type,
                consensus_states: Default::default(),
                client_state: Default::default(),
            });

        client_record.client_type = client_type;
        Ok(())
    }

    fn store_client_state(
        &mut self,
        client_id: ClientId,
        client_state: Box<dyn ClientState>,
    ) -> Result<(), Ics02Error> {
        let mut ibc_store = self.ibc_store.lock().unwrap();
        let client_record = ibc_store
            .clients
            .entry(client_id)
            .or_insert(MockClientRecord {
                client_type: client_state.client_type(),
                consensus_states: Default::default(),
                client_state: Default::default(),
            });

        client_record.client_state = Some(client_state);
        Ok(())
    }

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        height: Height,
        consensus_state: Box<dyn ConsensusState>,
    ) -> Result<(), Ics02Error> {
        let mut ibc_store = self.ibc_store.lock().unwrap();
        let client_record = ibc_store
            .clients
            .entry(client_id)
            .or_insert(MockClientRecord {
                client_type: ClientType::Mock,
                consensus_states: Default::default(),
                client_state: Default::default(),
            });

        client_record
            .consensus_states
            .insert(height, consensus_state);
        Ok(())
    }

    fn increase_client_counter(&mut self) {
        self.ibc_store.lock().unwrap().client_ids_counter += 1
    }

    fn store_update_time(
        &mut self,
        client_id: ClientId,
        height: Height,
        timestamp: Timestamp,
    ) -> Result<(), Ics02Error> {
        let _ = self
            .ibc_store
            .lock()
            .unwrap()
            .client_processed_times
            .insert((client_id, height), timestamp);
        Ok(())
    }

    fn store_update_height(
        &mut self,
        client_id: ClientId,
        height: Height,
        host_height: Height,
    ) -> Result<(), Ics02Error> {
        let _ = self
            .ibc_store
            .lock()
            .unwrap()
            .client_processed_heights
            .insert((client_id, height), host_height);
        Ok(())
    }
}

impl Ics18Context for MockContext {
    fn query_latest_height(&self) -> Height {
        self.host_current_height()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<Box<dyn ClientState>> {
        // Forward call to Ics2.
        ClientReader::client_state(self, client_id).ok()
    }

    fn query_latest_header(&self) -> Option<Box<dyn Header>> {
        let block_ref = self.host_block(self.host_current_height());
        block_ref.cloned().map(Header::into_box)
    }

    fn send(&mut self, msgs: Vec<Any>) -> Result<Vec<IbcEvent>, Ics18Error> {
        // Forward call to Ics26 delivery method.
        let mut all_events = vec![];
        for msg in msgs {
            let MsgReceipt { mut events, .. } =
                deliver(self, msg).map_err(Ics18Error::transaction_failed)?;
            all_events.append(&mut events);
        }
        self.advance_host_chain_height(); // Advance chain height
        Ok(all_events)
    }

    fn signer(&self) -> Signer {
        "0CDA3F47EF3C4906693B170EF650EB968C5F4B2C".parse().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use alloc::str::FromStr;

    use crate::core::ics04_channel::channel::{Counterparty, Order};
    use crate::core::ics04_channel::error::Error;
    use crate::core::ics04_channel::packet::Packet;
    use crate::core::ics04_channel::Version;
    use crate::core::ics24_host::identifier::ChainId;
    use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
    use crate::core::ics26_routing::context::{
        Acknowledgement, Module, ModuleId, ModuleOutputBuilder, OnRecvPacketAck, Router,
        RouterBuilder,
    };
    use crate::mock::context::MockContext;
    use crate::mock::context::MockRouterBuilder;
    use crate::mock::host::HostType;
    use crate::prelude::*;
    use crate::signer::Signer;
    use crate::test_utils::get_dummy_bech32_account;
    use crate::Height;

    #[test]
    fn test_history_manipulation() {
        pub struct Test {
            name: String,
            ctx: MockContext,
        }
        let cv = 1; // The version to use for all chains.

        let tests: Vec<Test> = vec![
            Test {
                name: "Empty history, small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    2,
                    Height::new(cv, 1).unwrap(),
                ),
            },
            Test {
                name: "[Synthetic TM host] Empty history, small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mocksgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    2,
                    Height::new(cv, 1).unwrap(),
                ),
            },
            Test {
                name: "Large pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    30,
                    Height::new(cv, 2).unwrap(),
                ),
            },
            Test {
                name: "[Synthetic TM host] Large pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mocksgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    30,
                    Height::new(cv, 2).unwrap(),
                ),
            },
            Test {
                name: "Small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    3,
                    Height::new(cv, 30).unwrap(),
                ),
            },
            Test {
                name: "[Synthetic TM host] Small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    3,
                    Height::new(cv, 30).unwrap(),
                ),
            },
            Test {
                name: "Small pruning window, small starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    3,
                    Height::new(cv, 2).unwrap(),
                ),
            },
            Test {
                name: "[Synthetic TM host] Small pruning window, small starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    3,
                    Height::new(cv, 2).unwrap(),
                ),
            },
            Test {
                name: "Large pruning window, large starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    50,
                    Height::new(cv, 2000).unwrap(),
                ),
            },
            Test {
                name: "[Synthetic TM host] Large pruning window, large starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    50,
                    Height::new(cv, 2000).unwrap(),
                ),
            },
        ];

        for mut test in tests {
            // All tests should yield a valid context after initialization.
            assert!(
                test.ctx.validate().is_ok(),
                "failed in test {} while validating context {:?}",
                test.name,
                test.ctx
            );

            let current_height = test.ctx.latest_height();

            // After advancing the chain's height, the context should still be valid.
            test.ctx.advance_host_chain_height();
            assert!(
                test.ctx.validate().is_ok(),
                "failed in test {} while validating context {:?}",
                test.name,
                test.ctx
            );

            let next_height = current_height.increment();
            assert_eq!(
                test.ctx.latest_height(),
                next_height,
                "failed while increasing height for context {:?}",
                test.ctx
            );

            assert_eq!(
                test.ctx.host_block(current_height).unwrap().height(),
                current_height,
                "failed while fetching height {:?} of context {:?}",
                current_height,
                test.ctx
            );
        }
    }

    #[test]
    fn test_router() {
        #[derive(Default)]
        struct MockAck(Vec<u8>);

        impl AsRef<[u8]> for MockAck {
            fn as_ref(&self) -> &[u8] {
                self.0.as_slice()
            }
        }

        impl Acknowledgement for MockAck {}

        #[derive(Debug, Default)]
        struct FooModule {
            counter: usize,
        }

        impl Module for FooModule {
            fn on_chan_open_try(
                &mut self,
                _output: &mut ModuleOutputBuilder,
                _order: Order,
                _connection_hops: &[ConnectionId],
                _port_id: &PortId,
                _channel_id: &ChannelId,
                _counterparty: &Counterparty,
                _version: &Version,
                counterparty_version: &Version,
            ) -> Result<Version, Error> {
                Ok(counterparty_version.clone())
            }

            fn on_recv_packet(
                &self,
                _output: &mut ModuleOutputBuilder,
                _packet: &Packet,
                _relayer: &Signer,
            ) -> OnRecvPacketAck {
                OnRecvPacketAck::Successful(
                    Box::new(MockAck::default()),
                    Box::new(|module| {
                        let module = module.downcast_mut::<FooModule>().unwrap();
                        module.counter += 1;
                        Ok(())
                    }),
                )
            }
        }

        #[derive(Debug, Default)]
        struct BarModule;

        impl Module for BarModule {
            fn on_chan_open_try(
                &mut self,
                _output: &mut ModuleOutputBuilder,
                _order: Order,
                _connection_hops: &[ConnectionId],
                _port_id: &PortId,
                _channel_id: &ChannelId,
                _counterparty: &Counterparty,
                _version: &Version,
                counterparty_version: &Version,
            ) -> Result<Version, Error> {
                Ok(counterparty_version.clone())
            }
        }

        let r = MockRouterBuilder::default()
            .add_route("foomodule".parse().unwrap(), FooModule::default())
            .unwrap()
            .add_route("barmodule".parse().unwrap(), BarModule::default())
            .unwrap()
            .build();

        let mut ctx = MockContext::new(
            ChainId::new("mockgaia".to_string(), 1),
            HostType::Mock,
            1,
            Height::new(1, 1).unwrap(),
        )
        .with_router(r);

        let mut on_recv_packet_result = |module_id: &'static str| {
            let module_id = ModuleId::from_str(module_id).unwrap();
            let m = ctx.router.get_route_mut(&module_id).unwrap();
            let result = m.on_recv_packet(
                &mut ModuleOutputBuilder::new(),
                &Packet::default(),
                &get_dummy_bech32_account().parse().unwrap(),
            );
            (module_id, result)
        };

        let results = vec![
            on_recv_packet_result("foomodule"),
            on_recv_packet_result("barmodule"),
        ];
        results
            .into_iter()
            .filter_map(|(mid, result)| match result {
                OnRecvPacketAck::Nil(write_fn) | OnRecvPacketAck::Successful(_, write_fn) => {
                    Some((mid, write_fn))
                }
                _ => None,
            })
            .for_each(|(mid, write_fn)| {
                write_fn(ctx.router.get_route_mut(&mid).unwrap().as_any_mut()).unwrap()
            });
    }
}
