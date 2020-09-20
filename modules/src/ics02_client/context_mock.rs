use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::Error;
use crate::ics24_host::identifier::ClientId;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientRecord, MockClientState, MockConsensusState};
use std::collections::HashMap;
use tendermint::block::Height;

/// A mock implementation of client context. This mocks (i.e., replaces) the functionality of
/// a KV-store holding information related to the various IBC clients running on a chain.
/// Each such client is represented here by a `MockClientRecord`.
/// Implements traits `ClientReader` and `ClientKeeper`, and is therefore useful for testing
/// the ICS02 handlers (create, update client) and other dependent ICS handlers (e.g., ICS03).
#[derive(Clone, Debug)]
pub struct MockClientContext {
    /// The set of all clients, indexed by their id.
    pub clients: HashMap<ClientId, MockClientRecord>,
}

impl Default for MockClientContext {
    fn default() -> Self {
        MockClientContext {
            clients: Default::default(),
        }
    }
}

impl MockClientContext {
    /// Given a client id, a type, and a height, registers a new client of the given type in the
    /// context. The client will have mock client state and a mock consensus state for the given
    /// height.
    pub fn with_client(&mut self, client_id: &ClientId, client_type: ClientType, h: Height) {
        let mut client_record = MockClientRecord {
            client_type,
            client_state: MockClientState(MockHeader(h)),
            consensus_states: HashMap::with_capacity(1),
        };
        client_record
            .consensus_states
            .insert(h, MockConsensusState(MockHeader(h)));
        self.clients.insert(client_id.clone(), client_record);
    }

    /// Given a client type, an id, and a height, this function registers in the context a new
    /// client record for that type and id. This client record will have no consensus states, and a
    /// default client state for the input height.
    pub fn with_client_type(&mut self, client_id: &ClientId, client_type: ClientType, h: Height) {
        let client_record = MockClientRecord {
            client_type,
            client_state: MockClientState(MockHeader(h)),
            consensus_states: Default::default(),
        };
        self.clients.insert(client_id.clone(), client_record);
    }

    /// Given a client id and a height, registers a new client in the context and also associates
    /// to this client a mock client state and a mock consensus state for the input height. The type
    /// of this client is implicitly assumed to be Mock.
    pub fn with_client_consensus_state(&mut self, client_id: &ClientId, h: Height) {
        let mut client_record = MockClientRecord {
            client_type: ClientType::Mock,
            client_state: MockClientState(MockHeader(h)),
            consensus_states: HashMap::with_capacity(1),
        };
        client_record
            .consensus_states
            .insert(h, MockConsensusState(MockHeader(h)));
        self.clients.insert(client_id.clone(), client_record);
    }
}

impl ClientReader for MockClientContext {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        match self.clients.get(client_id) {
            Some(client_record) => client_record.client_type.into(),
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
            // client_record.consensus_states.get(&height).map(Option::from),
            None => None,
        }
    }
}

impl ClientKeeper for MockClientContext {
    fn store_client_type(
        &mut self,
        _client_id: ClientId,
        _client_type: ClientType,
    ) -> Result<(), Error> {
        todo!()
    }

    fn store_client_state(
        &mut self,
        _client_id: ClientId,
        _client_state: AnyClientState,
    ) -> Result<(), Error> {
        todo!()
    }

    fn store_consensus_state(
        &mut self,
        _client_id: ClientId,
        _consensus_state: AnyConsensusState,
    ) -> Result<(), Error> {
        todo!()
    }
}
