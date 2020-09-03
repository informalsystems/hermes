use crate::context::{ChainReader, SelfHeader};
use crate::context_mock::MockChainContext;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::context::ClientReader;
use crate::ics02_client::context_mock::MockClientContext;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use std::collections::HashMap;
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq)]
pub struct MockConnectionContext {
    chain_context: MockChainContext,
    client_context: MockClientContext,
    connections: HashMap<ConnectionId, ConnectionEnd>,
}

impl MockConnectionContext {
    pub fn new(chain_height: u64, max_history_size: usize) -> Self {
        MockConnectionContext {
            chain_context: MockChainContext::new(max_history_size, Height(chain_height)),
            client_context: Default::default(),
            connections: Default::default(),
        }
    }

    pub fn with_client_state(&mut self, client_id: &ClientId, latest_client_height: u64) {
        self.client_context
            .with_client_state(client_id, latest_client_height)
    }

    pub fn max_size(&self) -> usize {
        self.chain_context.max_size()
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

    fn fetch_client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.client_context.client_state(client_id)
    }

    fn chain_current_height(&self) -> Height {
        self.chain_context.latest
    }

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> usize {
        self.chain_context.max_size()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        unimplemented!()
    }

    fn fetch_client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState> {
        self.client_context.consensus_state(client_id, height)
    }

    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState> {
        let hi = self.chain_context.self_historical_info(height)?.header;
        match hi {
            #[cfg(test)]
            SelfHeader::Mock(h) => Some(h.into()),
        }
    }
}

impl ConnectionKeeper for MockConnectionContext {
    fn store_connection(
        &mut self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Result<(), Error> {
        self.connections.insert(connection_id, connection_end);
        Ok(())
    }
}
