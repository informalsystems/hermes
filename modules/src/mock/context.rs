//! Implementation of a global context mock. Used in testing handlers of all IBC modules.
use crate::prelude::*;

use alloc::{collections::btree_map::BTreeMap, sync::Arc};
use core::{
	borrow::Borrow,
	cmp::min,
	fmt::{Debug, Formatter},
	ops::{Add, Sub},
	time::Duration,
};
use std::{marker::PhantomData, sync::Mutex};

use crate::core::ics02_client::{client_consensus::ConsensusState, client_def::ClientDef};
use ibc_proto::google::protobuf::Any;
use sha2::Digest;
use tracing::debug;

#[cfg(test)]
use crate::core::ics02_client::events::Attributes;
use crate::{
	core::{
		ics02_client::{
			client_message::ClientMessage,
			client_state::{ClientState, ClientType},
			context::{ClientKeeper, ClientReader},
			error::Error as Ics02Error,
		},
		ics03_connection::{
			connection::ConnectionEnd,
			context::{ConnectionKeeper, ConnectionReader},
			error::Error as Ics03Error,
		},
		ics04_channel::{
			channel::ChannelEnd,
			commitment::{AcknowledgementCommitment, PacketCommitment},
			context::{ChannelKeeper, ChannelReader},
			error::Error as Ics04Error,
			packet::{Receipt, Sequence},
		},
		ics05_port::{
			context::PortReader,
			error::{Error as Ics05Error, Error},
		},
		ics23_commitment::commitment::CommitmentPrefix,
		ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId},
		ics26_routing::{
			context::{Ics26Context, Module, ModuleId, ReaderContext, Router, RouterBuilder},
			error::Error as Ics26Error,
			handler::dispatch,
			msgs::Ics26Envelope,
		},
	},
	mock::{
		client_def::AnyClient,
		client_state::{
			AnyClientState, AnyConsensusState, AnyConsensusStateWithHeight, MockClientRecord,
			MockClientState, MockConsensusState,
		},
		header::{AnyClientMessage, MockHeader},
		host::{HostBlock, MockHostBlock},
	},
	timestamp::Timestamp,
	Height,
};

pub const DEFAULT_BLOCK_TIME_SECS: u64 = 3;

/// A context implementing the dependencies necessary for testing any IBC module.
#[derive(Debug)]
pub struct MockContext<C: ClientTypes = MockClientTypes> {
	/// The type of host chain underlying this mock context.
	pub host_chain_type: <C::HostBlock as HostBlock>::HostType,

	/// Host chain identifier.
	pub host_chain_id: ChainId,

	/// Maximum size for the history of the host chain. Any block older than this is pruned.
	pub max_history_size: usize,

	/// The chain of blocks underlying this context. A vector of size up to `max_history_size`
	/// blocks, ascending order by their height (latest block is on the last position).
	pub history: Vec<C::HostBlock>,

	/// Average time duration between blocks
	pub block_time: Duration,

	/// An object that stores all IBC related data.
	pub ibc_store: Arc<Mutex<MockIbcStore<C>>>,

	/// ICS26 router impl
	pub router: MockRouter,

	pub _phantom: PhantomData<C>,
}

impl<C: ClientTypes> PartialEq for MockContext<C> {
	fn eq(&self, _other: &Self) -> bool {
		unimplemented!()
	}
}

impl<C: ClientTypes> Eq for MockContext<C> {}

/// Returns a MockContext with bare minimum initialization: no clients, no connections and no
/// channels are present, and the chain has Height(5). This should be used sparingly, mostly for
/// testing the creation of new domain objects.
impl<C: ClientTypes + Default> Default for MockContext<C> {
	fn default() -> Self {
		Self::new(
			ChainId::new("mockgaia".to_string(), 0),
			<C::HostBlock as HostBlock>::HostType::default(),
			5,
			Height::new(0, 5),
		)
	}
}

/// A manual clone impl is provided because the tests are oblivious to the fact that the `ibc_store`
/// is a shared ptr.
impl<C: ClientTypes> Clone for MockContext<C> {
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
			_phantom: Default::default(),
		}
	}
}

/// Implementation of internal interface for use in testing. The methods in this interface should
/// _not_ be accessible to any Ics handler.
impl<C: ClientTypes + Default> MockContext<C> {
	/// Creates a mock context. Parameter `max_history_size` determines how many blocks will
	/// the chain maintain in its history, which also determines the pruning window. Parameter
	/// `latest_height` determines the current height of the chain. This context
	/// has support to emulate two type of underlying chains: Mock or SyntheticTendermint.
	pub fn new(
		host_id: ChainId,
		host_type: <C::HostBlock as HostBlock>::HostType,
		max_history_size: usize,
		latest_height: Height,
	) -> Self {
		assert_ne!(max_history_size, 0, "The chain must have a non-zero max_history_size");

		assert_ne!(
			latest_height.revision_height, 0,
			"The chain must have a non-zero revision_height"
		);

		// Compute the number of blocks to store.
		let n = min(max_history_size as u64, latest_height.revision_height);

		assert_eq!(
			host_id.version(),
			latest_height.revision_number,
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
					<C::HostBlock>::generate_block(
						host_id.clone(),
						host_type,
						latest_height.sub(i).unwrap().revision_height,
						next_block_timestamp
							.sub(Duration::from_secs(DEFAULT_BLOCK_TIME_SECS * (i + 1)))
							.unwrap(),
					)
				})
				.collect(),
			block_time,
			ibc_store: Arc::new(Mutex::new(MockIbcStore::<C>::default())),
			router: Default::default(),
			_phantom: Default::default(),
		}
	}

	/// Associates a connection to this context.
	pub fn with_connection(
		self,
		connection_id: ConnectionId,
		connection_end: ConnectionEnd,
	) -> Self {
		self.ibc_store.lock().unwrap().connections.insert(connection_id, connection_end);
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
		channels.insert((port_id, chan_id), channel_end);
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
		next_sequence_send.insert((port_id, chan_id), seq_number);
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
		next_sequence_recv.insert((port_id, chan_id), seq_number);
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
		next_sequence_ack.insert((port_id, chan_id), seq_number);
		self.ibc_store.lock().unwrap().next_sequence_ack = next_sequence_ack;
		self
	}

	pub fn with_height(self, target_height: Height) -> Self {
		let latest_height = self.latest_height();
		if target_height.revision_number > latest_height.revision_number {
			unimplemented!()
		} else if target_height.revision_number < latest_height.revision_number {
			panic!("Cannot rewind history of the chain to a smaller revision number!")
		} else if target_height.revision_height < latest_height.revision_height {
			panic!("Cannot rewind history of the chain to a smaller revision height!")
		} else if target_height.revision_height > latest_height.revision_height {
			// Repeatedly advance the host chain height till we hit the desired height
			let mut ctx = MockContext { ..self };
			while ctx.latest_height().revision_height < target_height.revision_height {
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
		packet_commitment.insert((port_id, chan_id, seq), data);
		self.ibc_store.lock().unwrap().packet_commitment = packet_commitment;
		self
	}

	pub fn with_router(self, router: MockRouter) -> Self {
		Self { router, ..self }
	}

	/// Accessor for a block of the local (host) chain from this context.
	/// Returns `None` if the block at the requested height does not exist.
	pub fn host_block(&self, target_height: Height) -> Option<&C::HostBlock> {
		let target = target_height.revision_height as usize;
		let latest = self.latest_height().revision_height as usize;

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
		let new_block = <C as ClientTypes>::HostBlock::generate_block(
			self.host_chain_id.clone(),
			self.host_chain_type,
			latest_block.height().increment().revision_height,
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
	pub fn deliver(&mut self, msg: Ics26Envelope<MockContext<C>>) -> Result<(), Ics26Error> {
		dispatch(self, msg)?;
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
		self.ibc_store.lock().unwrap().port_to_module.insert(port_id, module_id);
	}

	pub fn scope_port_to_module(&mut self, port_id: PortId, module_id: ModuleId) {
		self.ibc_store.lock().unwrap().port_to_module.insert(port_id, module_id);
	}

	pub fn consensus_states(&self, client_id: &ClientId) -> Vec<AnyConsensusStateWithHeight<C>> {
		self.ibc_store.lock().unwrap().clients[client_id]
			.consensus_states
			.iter()
			.map(|(k, v)| AnyConsensusStateWithHeight { height: *k, consensus_state: v.clone() })
			.collect()
	}

	pub fn latest_client_states(&self, client_id: &ClientId) -> C::AnyClientState {
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
	) -> C::AnyConsensusState {
		self.ibc_store.lock().unwrap().clients[client_id]
			.consensus_states
			.get(height)
			.unwrap()
			.clone()
	}

	#[inline]
	pub fn latest_height(&self) -> Height {
		self.history.last().expect("history cannot be empty").height()
	}

	pub fn ibc_store_share(&self) -> Arc<Mutex<MockIbcStore<C>>> {
		self.ibc_store.clone()
	}
}

impl<C: ClientTypes + Default> MockContext<C>
where
	C::AnyClientState: From<MockClientState>,
	C::AnyConsensusState: From<MockConsensusState>,
{
	/// Associates a client record to this context.
	/// Given a client id and a height, registers a new client in the context and also associates
	/// to this client a mock client state and a mock consensus state for height `height`. The type
	/// of this client is implicitly assumed to be Mock.
	pub fn with_client(self, client_id: &ClientId, height: Height) -> Self {
		self.with_client_parametrized(
			client_id,
			height,
			Some(MockClientState::client_type()),
			Some(height),
		)
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

		let client_type = client_type.unwrap_or(MockClientState::client_type());
		let (client_state, consensus_state) = match client_type.clone() {
			// If it's a mock client, create the corresponding mock states.
			client_type if client_type == MockClientState::client_type() => (
				Some(MockClientState::new(MockHeader::new(client_state_height).into()).into()),
				MockConsensusState::new(MockHeader::new(cs_height)).into(),
			),
			_ => unimplemented!(),
		};
		let consensus_states = vec![(cs_height, consensus_state)].into_iter().collect();

		debug!("consensus states: {:?}", consensus_states);

		let client_record = MockClientRecord { client_type, client_state, consensus_states };
		self.ibc_store.lock().unwrap().clients.insert(client_id.clone(), client_record);
		self
	}
}

/// An object that stores all IBC related data.
#[derive(Clone, Debug, Default)]
pub struct MockIbcStore<C: ClientTypes> {
	/// The set of all clients, indexed by their id.
	pub clients: BTreeMap<ClientId, MockClientRecord<C>>,

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
	pub channels: BTreeMap<(PortId, ChannelId), ChannelEnd>,

	/// Tracks the sequence number for the next packet to be sent.
	pub next_sequence_send: BTreeMap<(PortId, ChannelId), Sequence>,

	/// Tracks the sequence number for the next packet to be received.
	pub next_sequence_recv: BTreeMap<(PortId, ChannelId), Sequence>,

	/// Tracks the sequence number for the next packet to be acknowledged.
	pub next_sequence_ack: BTreeMap<(PortId, ChannelId), Sequence>,

	pub packet_acknowledgement: BTreeMap<(PortId, ChannelId, Sequence), AcknowledgementCommitment>,

	/// Maps ports to the the module that owns it
	pub port_to_module: BTreeMap<PortId, ModuleId>,

	/// Constant-size commitments to packets data fields
	pub packet_commitment: BTreeMap<(PortId, ChannelId, Sequence), PacketCommitment>,

	// Used by unordered channel
	pub packet_receipt: BTreeMap<(PortId, ChannelId, Sequence), Receipt>,
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

impl<C: ClientTypes + Default> ReaderContext for MockContext<C> {}

impl<C: ClientTypes + Default> Ics26Context for MockContext<C> {
	type Router = MockRouter;

	fn router(&self) -> &Self::Router {
		&self.router
	}

	fn router_mut(&mut self) -> &mut Self::Router {
		&mut self.router
	}
}

impl<C: ClientTypes> PortReader for MockContext<C> {
	fn lookup_module_by_port(&self, port_id: &PortId) -> Result<ModuleId, Error> {
		match self.ibc_store.lock().unwrap().port_to_module.get(port_id) {
			Some(mod_id) => Ok(mod_id.clone()),
			None => Err(Ics05Error::unknown_port(port_id.clone())),
		}
	}
}

impl<C: ClientTypes> ChannelReader for MockContext<C> {
	fn channel_end(&self, pcid: &(PortId, ChannelId)) -> Result<ChannelEnd, Ics04Error> {
		match self.ibc_store.lock().unwrap().channels.get(pcid) {
			Some(channel_end) => Ok(channel_end.clone()),
			None => Err(Ics04Error::channel_not_found(pcid.0.clone(), pcid.1)),
		}
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

	fn get_next_sequence_send(
		&self,
		port_channel_id: &(PortId, ChannelId),
	) -> Result<Sequence, Ics04Error> {
		match self.ibc_store.lock().unwrap().next_sequence_send.get(port_channel_id) {
			Some(sequence) => Ok(*sequence),
			None => Err(Ics04Error::missing_next_send_seq(port_channel_id.clone())),
		}
	}

	fn get_next_sequence_recv(
		&self,
		port_channel_id: &(PortId, ChannelId),
	) -> Result<Sequence, Ics04Error> {
		match self.ibc_store.lock().unwrap().next_sequence_recv.get(port_channel_id) {
			Some(sequence) => Ok(*sequence),
			None => Err(Ics04Error::missing_next_recv_seq(port_channel_id.clone())),
		}
	}

	fn get_next_sequence_ack(
		&self,
		port_channel_id: &(PortId, ChannelId),
	) -> Result<Sequence, Ics04Error> {
		match self.ibc_store.lock().unwrap().next_sequence_ack.get(port_channel_id) {
			Some(sequence) => Ok(*sequence),
			None => Err(Ics04Error::missing_next_ack_seq(port_channel_id.clone())),
		}
	}

	fn get_packet_commitment(
		&self,
		key: &(PortId, ChannelId, Sequence),
	) -> Result<PacketCommitment, Ics04Error> {
		match self.ibc_store.lock().unwrap().packet_commitment.get(key) {
			Some(commitment) => Ok(commitment.clone()),
			None => Err(Ics04Error::packet_commitment_not_found(key.2)),
		}
	}

	fn get_packet_receipt(
		&self,
		key: &(PortId, ChannelId, Sequence),
	) -> Result<Receipt, Ics04Error> {
		match self.ibc_store.lock().unwrap().packet_receipt.get(key) {
			Some(receipt) => Ok(receipt.clone()),
			None => Err(Ics04Error::packet_receipt_not_found(key.2)),
		}
	}

	fn get_packet_acknowledgement(
		&self,
		key: &(PortId, ChannelId, Sequence),
	) -> Result<AcknowledgementCommitment, Ics04Error> {
		match self.ibc_store.lock().unwrap().packet_acknowledgement.get(key) {
			Some(ack) => Ok(ack.clone()),
			None => Err(Ics04Error::packet_acknowledgement_not_found(key.2)),
		}
	}

	fn hash(&self, value: Vec<u8>) -> Vec<u8> {
		sha2::Sha256::digest(value).to_vec()
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
			None => Err(Ics04Error::processed_time_not_found(client_id.clone(), height)),
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
			None => Err(Ics04Error::processed_height_not_found(client_id.clone(), height)),
		}
	}

	fn channel_counter(&self) -> Result<u64, Ics04Error> {
		Ok(self.ibc_store.lock().unwrap().channel_ids_counter)
	}

	fn max_expected_time_per_block(&self) -> Duration {
		self.block_time
	}
}

impl<C: ClientTypes> ChannelKeeper for MockContext<C> {
	fn store_packet_commitment(
		&mut self,
		key: (PortId, ChannelId, Sequence),
		commitment: PacketCommitment,
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().packet_commitment.insert(key, commitment);
		Ok(())
	}

	fn store_packet_acknowledgement(
		&mut self,
		key: (PortId, ChannelId, Sequence),
		ack_commitment: AcknowledgementCommitment,
	) -> Result<(), Ics04Error> {
		self.ibc_store
			.lock()
			.unwrap()
			.packet_acknowledgement
			.insert(key, ack_commitment);
		Ok(())
	}

	fn delete_packet_acknowledgement(
		&mut self,
		key: (PortId, ChannelId, Sequence),
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().packet_acknowledgement.remove(&key);
		Ok(())
	}

	fn store_connection_channels(
		&mut self,
		cid: ConnectionId,
		port_channel_id: &(PortId, ChannelId),
	) -> Result<(), Ics04Error> {
		self.ibc_store
			.lock()
			.unwrap()
			.connection_channels
			.entry(cid)
			.or_insert_with(Vec::new)
			.push(port_channel_id.clone());
		Ok(())
	}

	fn store_channel(
		&mut self,
		port_channel_id: (PortId, ChannelId),
		channel_end: &ChannelEnd,
	) -> Result<(), Ics04Error> {
		self.ibc_store
			.lock()
			.unwrap()
			.channels
			.insert(port_channel_id, channel_end.clone());
		Ok(())
	}

	fn store_next_sequence_send(
		&mut self,
		port_channel_id: (PortId, ChannelId),
		seq: Sequence,
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().next_sequence_send.insert(port_channel_id, seq);
		Ok(())
	}

	fn store_next_sequence_recv(
		&mut self,
		port_channel_id: (PortId, ChannelId),
		seq: Sequence,
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().next_sequence_recv.insert(port_channel_id, seq);
		Ok(())
	}

	fn store_next_sequence_ack(
		&mut self,
		port_channel_id: (PortId, ChannelId),
		seq: Sequence,
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().next_sequence_ack.insert(port_channel_id, seq);
		Ok(())
	}

	fn increase_channel_counter(&mut self) {
		self.ibc_store.lock().unwrap().channel_ids_counter += 1;
	}

	fn delete_packet_commitment(
		&mut self,
		key: (PortId, ChannelId, Sequence),
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().packet_commitment.remove(&key);
		Ok(())
	}

	fn store_packet_receipt(
		&mut self,
		key: (PortId, ChannelId, Sequence),
		receipt: Receipt,
	) -> Result<(), Ics04Error> {
		self.ibc_store.lock().unwrap().packet_receipt.insert(key, receipt);
		Ok(())
	}

	fn store_send_packet(
		&mut self,
		_key: (PortId, ChannelId, Sequence),
		_packet: crate::core::ics04_channel::packet::Packet,
	) -> Result<(), Ics04Error> {
		Ok(())
	}

	fn store_recv_packet(
		&mut self,
		_key: (PortId, ChannelId, Sequence),
		_packet: crate::core::ics04_channel::packet::Packet,
	) -> Result<(), Ics04Error> {
		Ok(())
	}
}

impl<C: ClientTypes> ConnectionReader for MockContext<C> {
	fn connection_end(&self, cid: &ConnectionId) -> Result<ConnectionEnd, Ics03Error> {
		match self.ibc_store.lock().unwrap().connections.get(cid) {
			Some(connection_end) => Ok(connection_end.clone()),
			None => Err(Ics03Error::connection_not_found(cid.clone())),
		}
	}

	fn host_oldest_height(&self) -> Height {
		// history must be non-empty, so `self.history[0]` is valid
		self.history[0].height()
	}

	fn commitment_prefix(&self) -> CommitmentPrefix {
		CommitmentPrefix::try_from(b"mock".to_vec()).unwrap()
	}

	fn connection_counter(&self) -> Result<u64, Ics03Error> {
		Ok(self.ibc_store.lock().unwrap().connection_ids_counter)
	}
}

impl<C: ClientTypes> ConnectionKeeper for MockContext<C> {
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

impl<C: ClientTypes + Default> ClientReader for MockContext<C> {
	fn client_type(&self, client_id: &ClientId) -> Result<ClientType, Ics02Error> {
		match self.ibc_store.lock().unwrap().clients.get(client_id) {
			Some(client_record) => Ok(client_record.client_type.clone()),
			None => Err(Ics02Error::client_not_found(client_id.clone())),
		}
	}

	fn client_state(&self, client_id: &ClientId) -> Result<C::AnyClientState, Ics02Error> {
		match self.ibc_store.lock().unwrap().clients.get(client_id) {
			Some(client_record) => client_record
				.client_state
				.clone()
				.ok_or_else(|| Ics02Error::client_not_found(client_id.clone())),
			None => Err(Ics02Error::client_not_found(client_id.clone())),
		}
	}

	fn consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<C::AnyConsensusState, Ics02Error> {
		match self.ibc_store.lock().unwrap().clients.get(client_id) {
			Some(client_record) => match client_record.consensus_states.get(&height) {
				Some(consensus_state) => Ok(consensus_state.clone()),
				None => Err(Ics02Error::consensus_state_not_found(client_id.clone(), height)),
			},
			None => Err(Ics02Error::consensus_state_not_found(client_id.clone(), height)),
		}
	}

	fn host_client_type(&self) -> String {
		MockClientState::client_type().to_owned()
	}

	/// Search for the lowest consensus state higher than `height`.
	fn next_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Option<C::AnyConsensusState>, Ics02Error> {
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
				return Ok(Some(client_record.consensus_states.get(&h).unwrap().clone()));
			}
		}
		Ok(None)
	}

	/// Search for the highest consensus state lower than `height`.
	fn prev_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Option<C::AnyConsensusState>, Ics02Error> {
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
				return Ok(Some(client_record.consensus_states.get(&h).unwrap().clone()));
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

	fn host_consensus_state(
		&self,
		height: Height,
		_proof: Option<Vec<u8>>,
	) -> Result<C::AnyConsensusState, Ics02Error> {
		match self.host_block(height) {
			Some(block_ref) => Ok(block_ref.clone().into()),
			None => Err(Ics02Error::missing_local_consensus_state(height)),
		}
	}

	fn client_counter(&self) -> Result<u64, Ics02Error> {
		Ok(self.ibc_store.lock().unwrap().client_ids_counter)
	}
}

#[derive(Debug, Eq, PartialEq, Clone, Default)]
pub struct MockClientTypes;

pub trait ClientTypes
where
	Self: Clone + Debug + Eq,
{
	type AnyClientMessage: ClientMessage
		+ TryFrom<Any, Error = Ics02Error>
		+ Into<Any>
		+ From<Self::HostBlock>;
	type AnyClientState: ClientState<ClientDef = Self::ClientDef>
		+ Eq
		+ TryFrom<Any, Error = Ics02Error>
		+ Into<Any>;
	type AnyConsensusState: ConsensusState
		+ Eq
		+ TryFrom<Any, Error = Ics02Error>
		+ Into<Any>
		+ From<Self::HostBlock>
		+ 'static;
	type ClientDef: ClientDef<
		ClientMessage = Self::AnyClientMessage,
		ClientState = Self::AnyClientState,
		ConsensusState = Self::AnyConsensusState,
	>;
	type HostBlock: HostBlock + Debug + Clone;
}

impl ClientTypes for MockClientTypes {
	type AnyClientMessage = AnyClientMessage;
	type AnyClientState = AnyClientState;
	type AnyConsensusState = AnyConsensusState;
	type ClientDef = AnyClient;
	type HostBlock = MockHostBlock;
}

impl<C: ClientTypes> ClientKeeper for MockContext<C> {
	type AnyClientMessage = C::AnyClientMessage;
	type AnyClientState = C::AnyClientState;
	type AnyConsensusState = C::AnyConsensusState;
	type ClientDef = C::ClientDef;

	fn store_client_type(
		&mut self,
		client_id: ClientId,
		client_type: ClientType,
	) -> Result<(), Ics02Error> {
		let mut ibc_store = self.ibc_store.lock().unwrap();
		let client_record = ibc_store.clients.entry(client_id).or_insert(MockClientRecord {
			client_type: client_type.clone(),
			consensus_states: Default::default(),
			client_state: Default::default(),
		});

		client_record.client_type = client_type;
		Ok(())
	}

	fn store_client_state(
		&mut self,
		client_id: ClientId,
		client_state: C::AnyClientState,
	) -> Result<(), Ics02Error> {
		let mut ibc_store = self.ibc_store.lock().unwrap();
		let client_record = ibc_store.clients.entry(client_id).or_insert(MockClientRecord {
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
		consensus_state: C::AnyConsensusState,
	) -> Result<(), Ics02Error> {
		let mut ibc_store = self.ibc_store.lock().unwrap();
		let client_record = ibc_store.clients.entry(client_id).or_insert(MockClientRecord {
			client_type: MockClientState::client_type(),
			consensus_states: Default::default(),
			client_state: Default::default(),
		});

		client_record.consensus_states.insert(height, consensus_state);
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

	fn validate_self_client(&self, _client_state: &C::AnyClientState) -> Result<(), Ics02Error> {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use test_log::test;

	use alloc::str::FromStr;

	use crate::{
		core::{
			ics04_channel::{
				channel::{Counterparty, Order},
				error::Error,
				packet::Packet,
				Version,
			},
			ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId},
			ics26_routing::context::{
				Acknowledgement, Module, ModuleId, ModuleOutputBuilder, OnRecvPacketAck, Router,
				RouterBuilder,
			},
		},
		mock::{
			context::{MockClientTypes, MockContext, MockRouterBuilder},
			host::{HostBlock, MockHostType},
		},
		prelude::*,
		signer::Signer,
		test_utils::get_dummy_bech32_account,
		Height,
	};

	#[test]
	fn test_history_manipulation() {
		pub struct Test {
			name: String,
			ctx: MockContext<MockClientTypes>,
		}
		let cv = 1; // The version to use for all chains.

		let tests: Vec<Test> = vec![
			Test {
				name: "Empty history, small pruning window".to_string(),
				ctx: MockContext::new(
					ChainId::new("mockgaia".to_string(), cv),
					MockHostType::Mock,
					2,
					Height::new(cv, 1),
				),
			},
			Test {
				name: "Large pruning window".to_string(),
				ctx: MockContext::new(
					ChainId::new("mockgaia".to_string(), cv),
					MockHostType::Mock,
					30,
					Height::new(cv, 2),
				),
			},
			Test {
				name: "Small pruning window".to_string(),
				ctx: MockContext::new(
					ChainId::new("mockgaia".to_string(), cv),
					MockHostType::Mock,
					3,
					Height::new(cv, 30),
				),
			},
			Test {
				name: "Small pruning window, small starting height".to_string(),
				ctx: MockContext::new(
					ChainId::new("mockgaia".to_string(), cv),
					MockHostType::Mock,
					3,
					Height::new(cv, 2),
				),
			},
			Test {
				name: "Large pruning window, large starting height".to_string(),
				ctx: MockContext::new(
					ChainId::new("mockgaia".to_string(), cv),
					MockHostType::Mock,
					50,
					Height::new(cv, 2000),
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
			if current_height > Height::new(cv, 0) {
				assert_eq!(
					test.ctx.host_block(current_height).unwrap().height(),
					current_height,
					"failed while fetching height {:?} of context {:?}",
					current_height,
					test.ctx
				);
			}
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

		let mut ctx = MockContext::<MockClientTypes>::new(
			ChainId::new("mockgaia".to_string(), 1),
			MockHostType::Mock,
			1,
			Height::new(1, 1),
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

		let results = vec![on_recv_packet_result("foomodule"), on_recv_packet_result("barmodule")];
		results
			.into_iter()
			.filter_map(|(mid, result)| match result {
				OnRecvPacketAck::Nil(write_fn) | OnRecvPacketAck::Successful(_, write_fn) => {
					Some((mid, write_fn))
				},
				_ => None,
			})
			.for_each(|(mid, write_fn)| {
				write_fn(ctx.router.get_route_mut(&mid).unwrap().as_any_mut()).unwrap()
			});
	}
}

#[cfg(test)]
impl Default for ClientId {
	fn default() -> Self {
		Self::new("07-tendermint", 0).unwrap()
	}
}

#[cfg(test)]
impl Default for Attributes {
	fn default() -> Self {
		Attributes {
			height: Height::default(),
			client_id: Default::default(),
			client_type: "07-tendermint".to_owned(),
			consensus_height: Height::default(),
		}
	}
}
