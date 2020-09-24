use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::ClientKeeper;
use crate::ics02_client::context_mock::MockClientContext;
use crate::ics02_client::error::Error;
use crate::ics03_connection::context_mock::MockConnectionContext;
use crate::ics24_host::identifier::ClientId;

/// Mock implementation of ICS26 context. Wraps around both a client (ICS2) and connections (ICS3)
/// contexts. TODO: this struct evolve as the routing module will capture more & more handlers.
#[derive(Clone, Debug)]
pub struct MockICS26Context {
    client_context: MockClientContext,
    connection_context: MockConnectionContext,
}

impl ClientKeeper for MockICS26Context {
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
