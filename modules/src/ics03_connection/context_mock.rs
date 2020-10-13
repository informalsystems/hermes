// TODO: This module is superseded by MockContext.
// Will be nuked soon with https://github.com/informalsystems/ibc-rs/issues/297.

use std::collections::HashMap;

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
use crate::Height;

#[derive(Clone, Debug, Default)]
pub struct MockConnectionContext {
    client_context: MockClientContext,
    connections: HashMap<ConnectionId, ConnectionEnd>,
    client_connections: HashMap<ClientId, ConnectionId>,
}

impl MockConnectionContext {
    pub fn new(chain_id: String, chain_height: Height, max_history_size: usize) -> Self {
        MockConnectionContext {
            client_context: MockClientContext::new(chain_id, chain_height, max_history_size),
            connections: Default::default(),
            client_connections: Default::default(),
        }
    }

    pub fn chain_context(&self) -> &MockChainContext {
        &self.client_context.chain_context
    }

    pub fn client_context(&self) -> &MockClientContext {
        &self.client_context
    }

    pub fn with_client_state(self, client_id: &ClientId, latest_client_height: u64) -> Self {
        let mut client_context = self.client_context().clone();
        client_context.with_client_consensus_state(
            client_id,
            Height {
                version_number: 0,
                version_height: latest_client_height,
            },
        );
        Self {
            client_context,
            ..self
        }
    }

    pub fn max_size(&self) -> usize {
        self.chain_context().max_size()
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
    fn connection_end(&self, cid: &ConnectionId) -> Option<&ConnectionEnd> {
        self.connections.get(cid)
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.client_context().client_state(client_id)
    }

    fn host_current_height(&self) -> Height {
        self.chain_context().latest
    }

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> usize {
        self.chain_context().max_size()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        CommitmentPrefix::from(vec![])
    }

    fn client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState> {
        self.client_context().consensus_state(client_id, height)
    }

    fn host_consensus_state(&self, height: Height) -> Option<AnyConsensusState> {
        let hi = self.chain_context().self_historical_info(height)?.header;
        match hi {
            #[cfg(test)]
            SelfHeader::Mock(h) => Some(h.into()),
            _ => None,
        }
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

impl ConnectionKeeper for MockConnectionContext {
    fn store_connection(
        &mut self,
        connection_id: &ConnectionId,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        self.connections
            .insert(connection_id.clone(), connection_end.clone());
        Ok(())
    }

    fn store_connection_to_client(
        &mut self,
        connection_id: &ConnectionId,
        client_id: &ClientId,
    ) -> Result<(), Error> {
        self.client_connections
            .insert(client_id.clone(), connection_id.clone());
        Ok(())
    }
}
