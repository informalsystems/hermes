use crate::ics02_client::context_mock::MockClientContext;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use std::collections::HashMap;
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq)]
pub struct MockConnectionContext {
    pub(crate) connections: HashMap<ConnectionId, ConnectionEnd>,
    client_reader: MockClientContext,
    chain_height: Height, // TODO - doesn't belong here
}

impl MockConnectionContext {
    pub fn new(client_id: &ClientId, chain_height: Height) -> Self {
        MockConnectionContext {
            connections: Default::default(),
            client_reader: MockClientContext::new(client_id),
            chain_height,
        }
    }

    pub fn add_connection(self, id: ConnectionId, end: ConnectionEnd) -> Self {
        let mut connections = self.connections.clone();
        connections.insert(id, end);
        Self {
            connections,
            ..self
        }
    }
}

impl ConnectionReader for MockConnectionContext {
    fn fetch_connection_end(&self, cid: &ConnectionId) -> Option<&ConnectionEnd> {
        self.connections.get(cid)
    }

    fn fetch_client_state(&self, _client_id: &ClientId) -> Option<&dyn ClientState> {
        unimplemented!()
    }

    fn chain_current_height(&self) -> Height {
        self.chain_height
    }

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> u32 {
        unimplemented!()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        unimplemented!()
    }

    fn fetch_client_consensus_state(
        &self,
        _client_id: &ClientId,
        _height: Height,
    ) -> Option<&dyn ConsensusState> {
        unimplemented!()
    }

    fn fetch_self_consensus_state(&self, _height: Height) -> Option<&dyn ConsensusState> {
        unimplemented!()
    }
}

impl ConnectionKeeper for MockConnectionContext {
    fn store_connection(
        &mut self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Result<(), Error> {
        let mut connections = self.connections.clone();
        connections.insert(connection_id, connection_end);
        Ok(())
    }
}
