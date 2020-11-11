//! Implementation of a global context mock. Used in testing handlers of all IBC modules.

use crate::ics02_client;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::{Error as ICS2Error, Kind as ICS2ErrorKind};
use crate::ics02_client::state::ClientState;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error as ICS3Error;
use crate::ics18_relayer::context::ICS18Context;
use crate::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::handler::dispatch;
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientRecord, MockClientState, MockConsensusState};
use crate::Height;

use std::cmp::min;
use std::collections::HashMap;
use std::error::Error;

#[derive(Clone, Debug)]
pub struct MockContext {
    /// Maximum size of the history.
    max_history_size: usize,

    /// Highest height of the headers in the history.
    latest_height: Height,

    /// A list of `max_history_size` headers, ascending order by their height (latest is last).
    history: Vec<MockHeader>,

    /// The set of all clients, indexed by their id.
    clients: HashMap<ClientId, MockClientRecord>,

    // Association between client ids and connection ids.
    client_connections: HashMap<ClientId, ConnectionId>,

    // All the connections in the store.
    connections: HashMap<ConnectionId, ConnectionEnd>,
}

/// Returns a MockContext with bare minimum initialization: no clients, no connections are
/// present, and the chain has Height(5). This should be used sparingly, mostly for testing the
/// creation of new domain objects.
impl Default for MockContext {
    fn default() -> Self {
        Self::new(5, Height::new(1, 5))
    }
}

/// Implementation of internal interface for use in testing. The methods in this interface should
/// _not_ be accessible to any ICS handler.
impl MockContext {
    /// Creates a mock context. Parameter `max_history_size` determines how many headers will
    /// the chain maintain in its history, which also determines the pruning window. Parameter
    /// `latest_height` determines the current height of the chain.
    pub fn new(max_history_size: usize, latest_height: Height) -> Self {
        // Compute the number of headers to store. If h is 0, nothing is stored.
        let n = min(max_history_size as u64, latest_height.version_height);

        assert_ne!(
            max_history_size, 0,
            "The chain must have a non-zero max_history_size"
        );

        MockContext {
            max_history_size,
            latest_height,
            history: (0..n)
                .rev()
                .map(|i| MockHeader(latest_height.sub(i).unwrap()))
                .collect(),
            connections: Default::default(),
            clients: Default::default(),
            client_connections: Default::default(),
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
        let mut clients = self.clients.clone();
        let cs_height = consensus_state_height.unwrap_or(client_state_height);

        let client_record = MockClientRecord {
            client_type: client_type.unwrap_or(ClientType::Mock),
            client_state: MockClientState(MockHeader(client_state_height)),
            consensus_states: vec![(cs_height, MockConsensusState(MockHeader(cs_height)))]
                .into_iter()
                .collect(),
        };
        clients.insert(client_id.clone(), client_record);

        Self { clients, ..self }
    }

    /// Associates a connection to this context.
    pub fn with_connection(
        self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Self {
        let mut connections = self.connections.clone();
        connections.insert(connection_id, connection_end);
        Self {
            connections,
            ..self
        }
    }

    /// Accessor for a header of the local (host) chain of this context.
    /// May return `None` if the header for the requested height does not exist.
    fn host_header(&self, target_height: Height) -> Option<MockHeader> {
        let target = target_height.version_height as usize;
        let latest = self.latest_height.version_height as usize;

        // Check that the header is not too advanced, nor has it been pruned.
        if (target > latest) || (target <= latest - self.history.len()) {
            None // Header for requested height does not exist in history.
        } else {
            Some(self.history[self.history.len() + target - latest - 1])
        }
    }

    /// Triggers the advancing of the host chain, by extending the history of blocks (headers).
    pub fn advance_host_chain_height(&mut self) {
        let new_header = MockHeader(self.latest_height.increment());

        // Append the new header at the tip of the history.
        if self.history.len() >= self.max_history_size {
            // History is full, we rotate and replace the tip with the new header.
            self.history.rotate_left(1);
            self.history[self.max_history_size - 1] = new_header;
        } else {
            // History is not full yet.
            self.history.push(new_header);
        }
        self.latest_height = new_header.height();
    }

    /// A datagram passes from the relayer to the IBC module (on host chain).
    /// Used in testing the ICS18 algorithms, hence this may return a ICS18Error.
    fn recv(&mut self, msg: ICS26Envelope) -> Result<(), ICS18Error> {
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
            // Get the highest header.
            let lh = self.history[self.history.len() - 1];
            // Check latest is properly updated with highest header height.
            if lh.height() != self.latest_height {
                return Err("latest height is not updated".to_string().into());
            }
        }

        // Check that headers in the history are in sequential order.
        for i in 1..self.history.len() {
            let ph = self.history[i - 1];
            let h = self.history[i];
            if ph.height().increment() != h.height() {
                return Err("headers in history not sequential".to_string().into());
            }
        }
        Ok(())
    }
}

impl ICS26Context for MockContext {}

impl ConnectionReader for MockContext {
    fn connection_end(&self, cid: &ConnectionId) -> Option<ConnectionEnd> {
        self.connections.get(cid).cloned()
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        // Forward method call to the ICS2 Client-specific method.
        ics02_client::context::ClientReader::client_state(self, client_id)
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
        let hi = self.host_header(height)?;
        Some(hi.into())
    }
}

impl ConnectionKeeper for MockContext {
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
            Some(client_record) => client_record.client_state.client_type().into(),
            None => None,
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        match self.clients.get(client_id) {
            Some(client_record) => Option::from(AnyClientState::Mock(client_record.client_state)),
            None => None,
        }
    }

    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState> {
        match self.clients.get(client_id) {
            Some(client_record) => match client_record.consensus_states.get(&height) {
                Some(consensus_state) => Option::from(AnyConsensusState::Mock(*consensus_state)),
                None => None,
            },
            None => None,
        }
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
        match client_state {
            AnyClientState::Mock(client_state) => {
                let mut client_record = self.clients.entry(client_id).or_insert(MockClientRecord {
                    client_type: ClientType::Mock,
                    consensus_states: Default::default(),
                    client_state,
                });
                client_record.client_state = client_state;
                Ok(())
            }
            _ => Err(ICS2ErrorKind::InvalidClientStateForStore.into()),
        }
    }

    fn store_consensus_state(
        &mut self,
        client_id: ClientId,
        height: Height,
        consensus_state: AnyConsensusState,
    ) -> Result<(), ICS2Error> {
        match consensus_state {
            AnyConsensusState::Mock(consensus_state) => {
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
            _ => Err(ICS2ErrorKind::InvalidClientStateForStore.into()),
        }
    }
}

impl ICS18Context for MockContext {
    fn query_latest_height(&self) -> Height {
        self.host_current_height()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        // Forward call to ICS2.
        ics02_client::context::ClientReader::client_state(self, client_id)
    }

    fn query_latest_header(&self) -> Option<AnyHeader> {
        let hi = self.host_header(self.host_current_height())?;
        Some(hi.into())
    }

    fn send(&mut self, msg: ICS26Envelope) -> Result<(), ICS18Error> {
        self.recv(msg)
    }
}

#[cfg(test)]
mod tests {
    use crate::mock_context::MockContext;
    use crate::Height;

    #[test]
    fn test_mock_context_history_manipulation() {
        pub struct Test {
            name: String,
            ctx: MockContext,
        }
        let cv = 1; // The version to use for all chains.

        let tests: Vec<Test> = vec![
            Test {
                name: "Empty history, small pruning window".to_string(),
                ctx: MockContext::new(1, Height::new(cv, 0)),
            },
            Test {
                name: "Large pruning window".to_string(),
                ctx: MockContext::new(30, Height::new(cv, 2)),
            },
            Test {
                name: "Small pruning window".to_string(),
                ctx: MockContext::new(3, Height::new(cv, 30)),
            },
            Test {
                name: "Small pruning window, small starting height".to_string(),
                ctx: MockContext::new(3, Height::new(cv, 2)),
            },
            Test {
                name: "Large pruning window, large starting height".to_string(),
                ctx: MockContext::new(50, Height::new(cv, 2000)),
            },
        ];

        for mut test in tests {
            // All tests should yield a valid context after initialization.
            assert!(
                test.ctx.validate().is_ok(),
                "Failed ({}) while validating context {:?}",
                test.name,
                test.ctx
            );

            let current_height = test.ctx.latest_height;

            // After advancing the chain's height, the context should still be valid.
            test.ctx.advance_host_chain_height();
            assert!(
                test.ctx.validate().is_ok(),
                "Failed while validating context {:?}",
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
                    test.ctx.host_header(current_height).unwrap().height(),
                    current_height,
                    "Failed while fetching height {:?} of context {:?}",
                    current_height,
                    test.ctx
                );
            }
        }
    }
}
