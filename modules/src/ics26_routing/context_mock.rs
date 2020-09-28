use crate::context::SelfChainType;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::context_mock::MockClientContext;
use crate::ics02_client::error::Error as ICS2Error;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics03_connection::context_mock::MockConnectionContext;
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics26_routing::context::ICS26Context;
use tendermint::block::Height;

/// Mock implementation of ICS26 context. Wraps around both a client (ICS2) and connections (ICS3)
/// contexts.
/// To fulfil the `ConnectionReader`, `ConnectionKeeper`, `ClientReader` and `ClientKeeper` traits,
/// we simply forward each method call to the inner `connection_context` or `client_context` member
/// of this mock type.
#[derive(Clone, Debug, Default)]
pub struct MockICS26Context {
    client_context: MockClientContext,
    connection_context: MockConnectionContext,
}

impl ICS26Context for MockICS26Context {}

impl ConnectionReader for MockICS26Context {
    fn fetch_connection_end(&self, conn_id: &ConnectionId) -> Option<&ConnectionEnd> {
        self.connection_context.fetch_connection_end(conn_id)
    }

    fn fetch_client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.connection_context.fetch_client_state(client_id)
    }

    fn chain_current_height(&self) -> Height {
        self.connection_context.chain_current_height()
    }

    fn chain_consensus_states_history_size(&self) -> usize {
        self.connection_context
            .chain_consensus_states_history_size()
    }

    fn chain_type(&self) -> SelfChainType {
        self.connection_context.chain_type()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        self.connection_context.commitment_prefix()
    }

    fn fetch_client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState> {
        self.connection_context
            .fetch_client_consensus_state(client_id, height)
    }

    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState> {
        self.connection_context.fetch_self_consensus_state(height)
    }

    fn get_compatible_versions(&self) -> Vec<String> {
        self.connection_context.get_compatible_versions()
    }

    fn pick_version(&self, counterparty_candidate_versions: Vec<String>) -> String {
        self.connection_context
            .pick_version(counterparty_candidate_versions)
    }
}

impl ClientReader for MockICS26Context {
    fn client_type(&self, client_id: &ClientId) -> Option<ClientType> {
        self.client_context.client_type(client_id)
    }

    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        self.client_context.client_state(client_id)
    }

    fn consensus_state(&self, client_id: &ClientId, height: Height) -> Option<AnyConsensusState> {
        self.client_context.consensus_state(client_id, height)
    }
}

impl ConnectionKeeper for MockICS26Context {
    fn store_connection(
        &mut self,
        _connection_id: &ConnectionId,
        _connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        unimplemented!()
    }

    fn store_connection_to_client(
        &mut self,
        _connection_id: &ConnectionId,
        _client_id: &ClientId,
    ) -> Result<(), Error> {
        unimplemented!()
    }
}

impl ClientKeeper for MockICS26Context {
    fn store_client_type(
        &mut self,
        _client_id: ClientId,
        _client_type: ClientType,
    ) -> Result<(), ICS2Error> {
        Ok(())
    }

    fn store_client_state(
        &mut self,
        _client_id: ClientId,
        _client_state: AnyClientState,
    ) -> Result<(), ICS2Error> {
        Ok(())
    }

    fn store_consensus_state(
        &mut self,
        _client_id: ClientId,
        _consensus_state: AnyConsensusState,
    ) -> Result<(), ICS2Error> {
        Ok(())
    }
}
