use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::error::Error;
use crate::ics24_host::identifier::ClientId;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};
use std::collections::HashMap;
use tendermint::block::Height;

/// A mock implementation of client context. Implements traits `ClientReader`
/// and `ClientKeeper`, and is therefore useful for testing the ICS02 handlers (create, update
/// client) and other dependent ICS handlers (e.g., ICS03).
#[derive(Clone, Debug, PartialEq)]
pub struct MockClientContext {
    /// The set of all clients, as well as their states, which this context comprises.
    pub client_states: HashMap<ClientId, MockClientState>,
    /// All clients in this context have this (same) type.
    pub client_type: Option<ClientType>,
    /// Mapping of heights to consensus states. All clients share these states. A future, more
    /// sophisticated implementation of this mock would permit individual sets of consensus states
    /// per client.
    pub consensus_states: HashMap<Height, MockConsensusState>,
}

impl Default for MockClientContext {
    fn default() -> Self {
        MockClientContext {
            client_states: Default::default(),
            client_type: None,
            consensus_states: Default::default(),
        }
    }
}

impl MockClientContext {
    pub fn with_client_type(&mut self, _client_id: &ClientId, client_type: ClientType) {
        // self.client_states.insert(*client_id, MockClientState(MockHeader(Height(h))));
        self.client_type = Option::from(client_type);
    }

    pub fn with_client_state(&mut self, client_id: &ClientId, h: u64) {
        self.client_type = Option::from(ClientType::Mock);
        self.client_states = HashMap::with_capacity(1);
        self.client_states
            .insert(client_id.clone(), MockClientState(MockHeader(Height(h))));
        self.consensus_states = HashMap::with_capacity(1);
        self.consensus_states
            .insert(Height(h), MockConsensusState(MockHeader(Height(h))));
    }
}

impl ClientReader for MockClientContext {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        match self.client_states.get(client_id) {
            Some(_) => self.client_type.clone(),
            None => None,
        }
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.client_states.get(client_id).copied().map(Into::into)
    }

    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState> {
        match self.client_states.get(client_id) {
            Some(_) => self.consensus_states.get(&height).copied().map(Into::into),
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
