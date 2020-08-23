use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::ICS3Context;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use std::collections::HashMap;
use tendermint::block::Height;

#[derive(Clone, Debug, Default)]
pub struct MockContext {
    store: HashMap<ConnectionId, ConnectionEnd>,
    chain_height: Height,
}

impl MockContext {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn set_chain_height(self, new_height: Height) -> Self {
        Self {
            chain_height: new_height,
            ..self
        }
    }

    pub(crate) fn add_connection_to_store(self, id: ConnectionId, end: ConnectionEnd) -> Self {
        let mut store = self.store.clone();
        store.insert(id, end);
        Self { store, ..self }
    }
}

impl ICS3Context for MockContext {
    fn fetch_connection_end(&self, cid: &ConnectionId) -> Option<&ConnectionEnd> {
        self.store.get(cid)
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
