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
use crate::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::handler::dispatch;
use crate::ics26_routing::msgs::ICS26Envelope;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientRecord, MockClientState, MockConsensusState};
use crate::Height;

use std::cmp::min;
use std::collections::HashMap;
use std::str::FromStr;

/// Mock for a context. Used in testing handlers of all modules.
#[derive(Clone, Debug)]
pub struct MockContext {
    /// Chain identifier in the form <chain>-<version>.
    pub chain_id: ChainId,

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
        Self::new(ChainId::from_str("chainA-1").unwrap(), 5, Height::new(0, 1))
    }
}

/// Comprises an internal interfaces for use in testing. The methods in this interface should not
/// be accessible to any ICS handler.
impl MockContext {
    pub fn new(chain_id: ChainId, max_history_size: usize, latest_height: Height) -> Self {
        // Compute the number of headers to store. If h is 0, nothing is stored.
        let n = min(max_history_size as u64, latest_height.version_height);

        MockContext {
            chain_id,
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

    // This may be twisted:
    // host_consensus_state (ret AnyConsensusState)  -> MockHeader
    // query_latest_header (AnyHeader) -> MockHeader

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

    /// Triggers the advancing of the host chain, by extending the history of blocks (headers).
    pub fn advance_host_chain_height(&mut self) {
        let new_height = Height::new(
            ChainId::chain_version(self.chain_id.clone().to_string()),
            self.latest_height.increment().version_height,
        );
        let header = MockHeader(new_height);

        // let mut history = self.history.clone();
        if self.history.len() >= self.max_history_size {
            self.history.rotate_left(1);
            self.history[self.max_history_size - 1] = header;
        } else {
            self.history.push(header);
        }
        self.latest_height = new_height;
    }

    /// Internal interface. A datagram passes from the relayer to the IBC module (on host chain).
    fn recv(&mut self, msg: ICS26Envelope) -> Result<(), ICS18Error> {
        dispatch(self, msg).map_err(|e| ICS18ErrorKind::TransactionFailed.context(e))?;
        // Create a new block.
        self.advance_host_chain_height();
        Ok(())
    }
}

impl ICS26Context for MockContext {}

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
            _ => Err(ICS2ErrorKind::BadClientState.into()),
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
            _ => Err(ICS2ErrorKind::BadClientState.into()),
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
