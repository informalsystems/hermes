use crate::ics02_client;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientReader;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error as ICS3Error;
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientRecord, MockClientState, MockConsensusState};
use crate::Height;

use crate::ics02_client::state::ClientState;
use std::cmp::min;
use std::collections::HashMap;

/// Mock for a context. Used in testing handlers of all modules.
#[derive(Clone, Debug)]
pub struct MockContext {
    /// Maximum size of the history.
    max_history_size: usize,

    /// Highest height of the headers in the history.
    latest_height: Height,

    /// A list of `max_history_size` headers, ascending order by their height (latest is last).
    history: Vec<MockHeader>,

    // All the connections in the store.
    connections: HashMap<ConnectionId, ConnectionEnd>,

    /// The set of all clients, indexed by their id.
    clients: HashMap<ClientId, MockClientRecord>,

    // Association between client ids and connection ids.
    client_connections: HashMap<ClientId, ConnectionId>,
}

/// Returns a MockContext with bare minimum initialization: no clients, no connections are
/// present, and the chain has Height(1). This should be used sparingly, mostly for testing the
/// creation of new domain objects.
impl Default for MockContext {
    fn default() -> Self {
        Self::new(5, Height::new(0, 1))
    }
}

impl MockContext {
    pub fn new(max_history_size: usize, latest_height: Height) -> Self {
        // Compute the number of headers to store. If h is 0, nothing is stored.
        let n = min(max_history_size as u64, latest_height.version_height);

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

    /// Internal interface for associating a client record to this context.
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

    /// Internal interface for associating a connection to this context.
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

    /// Internal interface. Accessor for a header of the local (host) chain of this context.
    /// May return `None` if the header for the requested height does not exist.
    fn host_header(&self, height: Height) -> Option<MockHeader> {
        let l = height.version_height as usize;
        let h = self.latest_height.version_height as usize;

        if l <= h - self.max_history_size {
            None // Header for requested height does not exist in the history.
        } else {
            Some(self.history[self.max_history_size + l - h - 1])
        }
    }
}

impl ConnectionReader for MockContext {
    fn connection_end(&self, cid: &ConnectionId) -> Option<&ConnectionEnd> {
        self.connections.get(cid)
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        // Forward method call to the ICS2 Client-specific method.
        ics02_client::context::ClientReader::client_state(self, client_id)
    }

    fn host_current_height(&self) -> Height {
        self.latest_height
    }

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> usize {
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

    fn get_compatible_versions(&self) -> Vec<String> {
        vec!["test".to_string()]
    }

    fn pick_version(&self, counterparty_candidate_versions: Vec<String>) -> String {
        counterparty_candidate_versions
            .get(0)
            .unwrap_or(&String::from("none"))
            .to_string()
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
