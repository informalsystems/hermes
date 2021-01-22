//! Implementation of a global context mock. Used in testing handlers of all IBC modules.

use std::cmp::min;
use std::collections::HashMap;
use std::error::Error;
use std::str::FromStr;

use prost_types::Any;
use tendermint::account::Id;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::Error as ICS2Error;

use crate::ics05_port::capabilities::Capability;
use crate::ics05_port::context::PortReader;

use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error as ICS3Error;

use crate::events::IBCEvent;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::ics04_channel::error::Error as ICS4Error;
use crate::ics07_tendermint::client_state::test_util::get_dummy_tendermint_client_state;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::handler::{deliver, dispatch};
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::mock::client_state::{MockClientRecord, MockClientState, MockConsensusState};
use crate::mock::header::MockHeader;
use crate::mock::host::{HostBlock, HostType};
use crate::Height;

/// A context implementing the dependencies necessary for testing any IBC module.
#[derive(Clone, Debug)]
pub struct MockContext {
    /// The type of host chain underlying this mock context.
    host_chain_type: HostType,

    /// Host chain identifier.
    host_chain_id: ChainId,

    /// Maximum size for the history of the host chain. Any block older than this is pruned.
    max_history_size: usize,

    /// Highest height (i.e., most recent) of the blocks in the history.
    latest_height: Height,

    /// The chain of blocks underlying this context. A vector of size up to `max_history_size`
    /// blocks, ascending order by their height (latest block is on the last position).
    history: Vec<HostBlock>,

    /// The set of all clients, indexed by their id.
    clients: HashMap<ClientId, MockClientRecord>,

    /// Counter for the client identifiers, necessary for `increase_client_counter` and the
    /// `client_counter` methods.
    client_ids_counter: u64,

    /// Association between client ids and connection ids.
    client_connections: HashMap<ClientId, ConnectionId>,

    /// All the connections in the store.
    connections: HashMap<ConnectionId, ConnectionEnd>,

    /// All the channels in the store. TODO Make new key PortId X ChanneId
    channels: HashMap<(PortId, ChannelId), ChannelEnd>,

    /// Association between conection ids and channel ids.
    connection_channels: HashMap<ConnectionId, Vec<(PortId, ChannelId)>>,

    /// Tracks the sequence number for the next packet to be sent.
    next_sequence_send: HashMap<(PortId, ChannelId), u64>,

    /// Tracks the sequence number for the next packet to be received.
    next_sequence_recv: HashMap<(PortId, ChannelId), u64>,

    /// Tracks the sequence number for the next packet to be acknowledged.
    next_sequence_ack: HashMap<(PortId, ChannelId), u64>,

    /// Maps ports to their capabilities
    port_capabilities: HashMap<PortId, Capability>,

    /// Counter for connection identifiers (see `next_connection_id`).
    connection_ids_counter: u32,

    /// Counter for channel identifiers (see `next_channel_id`).
    channel_ids_counter: u32,
}

/// Returns a MockContext with bare minimum initialization: no clients, no connections and no channels are
/// present, and the chain has Height(5). This should be used sparingly, mostly for testing the
/// creation of new domain objects.
impl Default for MockContext {
    fn default() -> Self {
        Self::new(
            ChainId::new("mockgaia".to_string(), 1),
            HostType::Mock,
            5,
            Height::new(1, 5),
        )
    }
}

/// Implementation of internal interface for use in testing. The methods in this interface should
/// _not_ be accessible to any ICS handler.
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

        // Compute the number of blocks to store. If latest_height is 0, nothing is stored.
        let n = min(max_history_size as u64, latest_height.revision_height);

        assert_eq!(
            host_id.version(),
            latest_height.revision_number,
            "The version in the chain identifier must match the version in the latest height"
        );

        MockContext {
            host_chain_type: host_type,
            host_chain_id: host_id.clone(),
            max_history_size,
            latest_height,
            history: (0..n)
                .rev()
                .map(|i| {
                    HostBlock::generate_block(
                        host_id.clone(),
                        host_type,
                        latest_height.sub(i).unwrap().revision_height,
                    )
                })
                .collect(),
            connections: Default::default(),
            client_ids_counter: 0,
            clients: Default::default(),
            client_connections: Default::default(),
            channels: Default::default(),
            connection_channels: Default::default(),
            next_sequence_send: Default::default(),
            next_sequence_recv: Default::default(),
            next_sequence_ack: Default::default(),
            port_capabilities: Default::default(),
            connection_ids_counter: 0,
            channel_ids_counter: 0,
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
        mut self,
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
                Some(MockClientState(MockHeader(client_state_height)).into()),
                MockConsensusState(MockHeader(cs_height)).into(),
            ),
            // If it's a Tendermint client, we need TM states.
            ClientType::Tendermint => {
                let light_block = HostBlock::generate_tm_block(
                    self.host_chain_id.clone(),
                    cs_height.revision_height,
                );
                let consensus_state = AnyConsensusState::from(light_block.clone());
                let client_state =
                    get_dummy_tendermint_client_state(light_block.signed_header.header);

                // Return the tuple.
                (Some(client_state), consensus_state)
            }
        };
        let consensus_states = vec![(cs_height, consensus_state)].into_iter().collect();

        let client_record = MockClientRecord {
            client_type,
            client_state,
            consensus_states,
        };
        self.clients.insert(client_id.clone(), client_record);
        self
    }

    /// Associates a connection to this context.
    pub fn with_connection(
        mut self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Self {
        self.connections.insert(connection_id, connection_end);
        self
    }

    pub fn with_port_capability(mut self, port_id: PortId) -> Self {
        self.port_capabilities.insert(port_id, Capability::new());
        self
    }

    /// Accessor for a block of the local (host) chain from this context.
    /// Returns `None` if the block at the requested height does not exist.
    fn host_block(&self, target_height: Height) -> Option<&HostBlock> {
        let target = target_height.revision_height as usize;
        let latest = self.latest_height.revision_height as usize;

        // Check that the block is not too advanced, nor has it been pruned.
        if (target > latest) || (target <= latest - self.history.len()) {
            None // Block for requested height does not exist in history.
        } else {
            Some(&self.history[self.history.len() + target - latest - 1])
        }
    }

    /// Triggers the advancing of the host chain, by extending the history of blocks (or headers).
    pub fn advance_host_chain_height(&mut self) {
        let new_block = HostBlock::generate_block(
            self.host_chain_id.clone(),
            self.host_chain_type,
            self.latest_height.increment().revision_height,
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
        self.latest_height = self.latest_height.increment();
    }

    /// A datagram passes from the relayer to the IBC module (on host chain).
    /// Alternative method to `ICS18Context::send` that does not exercise any serialization.
    /// Used in testing the ICS18 algorithms, hence this may return a ICS18Error.
    pub fn deliver(&mut self, msg: ICS26Envelope) -> Result<(), ICS18Error> {
        dispatch(self, msg).map_err(|e| ICS18ErrorKind::TransactionFailed.context(e))?;
        // Create a new block.
        self.advance_host_chain_height();
        Ok(())
    }

    /// Validates this context. Should be called after the context is mutated by a test.
    pub fn validate(&self) -> Result<(), Box<dyn Error>> {
        // Check that the number of entries is not higher than window size.
        if self.history.len() > self.max_history_size {
            return Err("too many entries".to_string().into());
        }

        // Check the content of the history.
        if !self.history.is_empty() {
            // Get the highest block.
            let lh = &self.history[self.history.len() - 1];
            // Check latest is properly updated with highest header height.
            if lh.height() != self.latest_height {
                return Err("latest height is not updated".to_string().into());
            }
        }

        // Check that headers in the history are in sequential order.
        for i in 1..self.history.len() {
            let ph = &self.history[i - 1];
            let h = &self.history[i];
            if ph.height().increment() != h.height() {
                return Err("headers in history not sequential".to_string().into());
            }
        }
        Ok(())
    }

    pub fn add_port(&mut self, port_id: PortId) {
        self.port_capabilities.insert(port_id, Capability::new());
    }
}

impl ICS26Context for MockContext {}

impl PortReader for MockContext {
    fn lookup_module_by_port(&self, port_id: &PortId) -> Option<Capability> {
        self.port_capabilities.get(port_id).cloned()
    }

    fn autenthenticate(&self, _cap: &Capability, _port_id: &PortId) -> bool {
        true
    }
}

impl ChannelReader for MockContext {
    fn channel_end(&self, pcid: &(PortId, ChannelId)) -> Option<ChannelEnd> {
        self.channels.get(pcid).cloned()
    }

    fn connection_state(&self, cid: &ConnectionId) -> Option<ConnectionEnd> {
        self.connections.get(cid).cloned()
    }

    fn connection_channels(&self, cid: &ConnectionId) -> Option<Vec<(PortId, ChannelId)>> {
        self.connection_channels.get(cid).cloned()
    }

    fn channel_client_state(
        &self,
        port_channel_id: &(PortId, ChannelId),
    ) -> Option<AnyClientState> {
        let channel = self.channel_end(port_channel_id);
        match channel {
            Some(v) => {
                let cid = v.connection_hops().clone()[0].clone();
                let conn = self.connection_state(&cid);
                match conn {
                    Some(v) => ConnectionReader::client_state(self, &v.client_id().clone()),
                    None => panic!(),
                }
            }
            None => panic!(),
        }
    }

    fn channel_consensus_state(
        &self,
        port_channel_id: &(PortId, ChannelId),
        height: Height,
    ) -> Option<AnyConsensusState> {
        let channel = self.channel_end(port_channel_id).unwrap();
        let cid = channel.connection_hops()[0].clone();
        let conn = self.connection_state(&cid).unwrap();

        ConnectionReader::client_consensus_state(self, conn.client_id(), height)
    }

    fn port_capability(&self, port_id: &PortId) -> Option<Capability> {
        PortReader::lookup_module_by_port(self, port_id)
    }

    fn capability_authentification(&self, port_id: &PortId, cap: &Capability) -> bool {
        PortReader::autenthenticate(self, cap, port_id)
    }
}

impl ChannelKeeper for MockContext {
    fn next_channel_id(&mut self) -> ChannelId {
        let prefix = ChannelId::default().to_string();
        let suffix = self.channel_ids_counter;
        self.channel_ids_counter += 1;

        ChannelId::from_str(format!("{}-{}", prefix, suffix).as_str()).unwrap()
    }

    fn store_channel(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        channel_end: &ChannelEnd,
    ) -> Result<(), ICS4Error> {
        self.channels
            .insert(port_channel_id.clone(), channel_end.clone());
        Ok(())
    }
    fn store_next_sequence_send(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), ICS4Error> {
        self.next_sequence_send.insert(port_channel_id.clone(), seq);
        Ok(())
    }

    fn store_next_sequence_recv(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), ICS4Error> {
        self.next_sequence_recv.insert(port_channel_id.clone(), seq);
        Ok(())
    }

    fn store_next_sequence_ack(
        &mut self,
        port_channel_id: &(PortId, ChannelId),
        seq: u64,
    ) -> Result<(), ICS4Error> {
        self.next_sequence_ack.insert(port_channel_id.clone(), seq);
        Ok(())
    }

    fn store_connection_channels(
        &mut self,
        cid: &ConnectionId,
        port_channel_id: &(PortId, ChannelId),
    ) -> Result<(), ICS4Error> {
        match self.connection_channels.get(cid) {
            Some(v) => {
                let mut modv = v.clone();
                modv.push(port_channel_id.clone());
                self.connection_channels.remove(cid);
                self.connection_channels.insert(cid.clone(), modv);
            }
            None => {
                let mut modv = Vec::new();
                modv.push(port_channel_id.clone());
                self.connection_channels.insert(cid.clone(), modv);
            }
        }
        Ok(())
    }
}

impl ConnectionReader for MockContext {
    fn connection_end(&self, cid: &ConnectionId) -> Option<ConnectionEnd> {
        self.connections.get(cid).cloned()
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        // Forward method call to the ICS2 Client-specific method.
        ClientReader::client_state(self, client_id)
    }

    fn host_current_height(&self) -> Height {
        self.latest_height
    }

    /// Returns the number of consensus state historical entries for the local chain.
    fn host_chain_history_size(&self) -> usize {
        self.max_history_size
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        CommitmentPrefix::from(vec![])
    }

    fn client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState> {
        // Forward method call to the ICS2Client-specific method.
        self.consensus_state(client_id, height)
    }

    fn host_consensus_state(&self, height: Height) -> Option<AnyConsensusState> {
        let block_ref = self.host_block(height);
        block_ref.cloned().map(Into::into)
    }
}

impl ConnectionKeeper for MockContext {
    fn next_connection_id(&mut self) -> ConnectionId {
        let prefix = ConnectionId::default().to_string();
        let suffix = self.connection_ids_counter;
        self.connection_ids_counter += 1;

        ConnectionId::from_str(format!("{}-{}", prefix, suffix).as_str()).unwrap()
    }

    fn store_connection(
        &mut self,
        connection_id: &ConnectionId,
        connection_end: &ConnectionEnd,
    ) -> Result<(), ICS3Error> {
        self.connections
            .insert(connection_id.clone(), connection_end.clone());
        Ok(())
    }

    fn store_connection_to_client(
        &mut self,
        connection_id: &ConnectionId,
        client_id: &ClientId,
    ) -> Result<(), ICS3Error> {
        self.client_connections
            .insert(client_id.clone(), connection_id.clone());
        Ok(())
    }
}

impl ClientReader for MockContext {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        match self.clients.get(client_id) {
            Some(client_record) => client_record.client_type.into(),
            None => None,
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        match self.clients.get(client_id) {
            Some(client_record) => client_record.client_state.clone(),
            None => None,
        }
    }

    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState> {
        match self.clients.get(client_id) {
            Some(client_record) => match client_record.consensus_states.get(&height) {
                Some(consensus_state) => Option::from(consensus_state.clone()),
                None => None,
            },
            None => None,
        }
    }

    fn client_counter(&self) -> u64 {
        self.client_ids_counter
    }
}

impl ClientKeeper for MockContext {
    fn store_client_type(
        &mut self,
        client_id: ClientId,
        client_type: ClientType,
    ) -> Result<(), ICS2Error> {
        let mut client_record = self.clients.entry(client_id).or_insert(MockClientRecord {
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
        client_state: AnyClientState,
    ) -> Result<(), ICS2Error> {
        let mut client_record = self.clients.entry(client_id).or_insert(MockClientRecord {
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
        consensus_state: AnyConsensusState,
    ) -> Result<(), ICS2Error> {
        let client_record = self.clients.entry(client_id).or_insert(MockClientRecord {
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
        self.client_ids_counter += 1
    }
}

impl ICS18Context for MockContext {
    fn query_latest_height(&self) -> Height {
        self.host_current_height()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        // Forward call to ICS2.
        ClientReader::client_state(self, client_id)
    }

    fn query_latest_header(&self) -> Option<AnyHeader> {
        let block_ref = self.host_block(self.host_current_height());
        block_ref.cloned().map(Into::into)
    }

    fn send(&mut self, msgs: Vec<Any>) -> Result<Vec<IBCEvent>, ICS18Error> {
        // Forward call to ICS26 delivery method.
        let events =
            deliver(self, msgs).map_err(|e| ICS18ErrorKind::TransactionFailed.context(e))?;

        self.advance_host_chain_height(); // Advance chain height
        Ok(events)
    }

    fn signer(&self) -> Id {
        Id::from_str("0CDA3F47EF3C4906693B170EF650EB968C5F4B2C").unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::ics24_host::identifier::ChainId;
    use crate::mock::context::MockContext;
    use crate::mock::host::HostType;
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
                    1,
                    Height::new(cv, 0),
                ),
            },
            Test {
                name: "[Synthetic TM host] Empty history, small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mocksgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    1,
                    Height::new(cv, 0),
                ),
            },
            Test {
                name: "Large pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    30,
                    Height::new(cv, 2),
                ),
            },
            Test {
                name: "[Synthetic TM host] Large pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mocksgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    30,
                    Height::new(cv, 2),
                ),
            },
            Test {
                name: "Small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    3,
                    Height::new(cv, 30),
                ),
            },
            Test {
                name: "[Synthetic TM host] Small pruning window".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    3,
                    Height::new(cv, 30),
                ),
            },
            Test {
                name: "Small pruning window, small starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    3,
                    Height::new(cv, 2),
                ),
            },
            Test {
                name: "[Synthetic TM host] Small pruning window, small starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    3,
                    Height::new(cv, 2),
                ),
            },
            Test {
                name: "Large pruning window, large starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::Mock,
                    50,
                    Height::new(cv, 2000),
                ),
            },
            Test {
                name: "[Synthetic TM host] Large pruning window, large starting height".to_string(),
                ctx: MockContext::new(
                    ChainId::new("mockgaia".to_string(), cv),
                    HostType::SyntheticTendermint,
                    50,
                    Height::new(cv, 2000),
                ),
            },
        ];

        for mut test in tests {
            // All tests should yield a valid context after initialization.
            assert!(
                test.ctx.validate().is_ok(),
                "Failed in test {} while validating context {:?}",
                test.name,
                test.ctx
            );

            let current_height = test.ctx.latest_height;

            // After advancing the chain's height, the context should still be valid.
            test.ctx.advance_host_chain_height();
            assert!(
                test.ctx.validate().is_ok(),
                "Failed in test {} while validating context {:?}",
                test.name,
                test.ctx
            );

            let next_height = current_height.increment();
            assert_eq!(
                test.ctx.latest_height, next_height,
                "Failed while increasing height for context {:?}",
                test.ctx
            );
            if current_height > Height::new(cv, 0) {
                assert_eq!(
                    test.ctx.host_block(current_height).unwrap().height(),
                    current_height,
                    "Failed while fetching height {:?} of context {:?}",
                    current_height,
                    test.ctx
                );
            }
        }
    }
}
