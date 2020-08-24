use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics24_host::introspect::{current_height, get_commitment_prefix};
use crate::Height;

// TODO: Remove this once Romain's code kicks in.
pub struct Chain {}

// TODO: Both ConnectionReader & Context should be generic over Chain.
pub struct Context {
    local_chain: Chain,
}

/// A context supplying all the necessary dependencies for processing any `ICS3Msg`.
pub trait ConnectionReader {
    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn fetch_connection_end(&self, conn_id: &ConnectionId) -> Option<&ConnectionEnd>;

    /// Returns the ClientState for the given identifier `client_id`.
    fn fetch_client_state(&self, client_id: &ClientId) -> Option<&dyn ClientState>;

    /// Returns the current height of the local chain.
    fn chain_current_height(&self) -> Height;

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> u32;

    /// Returns the prefix that the local chain uses in the KV store.
    fn commitment_prefix(&self) -> CommitmentPrefix;

    /// Returns the ConsensusState of the local chain at a specific height.
    fn fetch_client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<&dyn ConsensusState>;

    fn fetch_self_consensus_state(&self, height: Height) -> Option<&dyn ConsensusState>;
}

pub trait ConnectionKeeper {
    fn store_connection(
        &mut self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Result<(), Error>;
}

impl ConnectionReader for Context {
    fn fetch_connection_end(&self, _cid: &ConnectionId) -> Option<&ConnectionEnd> {
        unimplemented!()
    }

    fn fetch_client_state(&self, _client_id: &ClientId) -> Option<&dyn ClientState> {
        unimplemented!()
    }

    fn chain_current_height(&self) -> Height {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        current_height()
    }

    fn chain_consensus_states_history_size(&self) -> u32 {
        unimplemented!()
    }

    fn commitment_prefix(&self) -> CommitmentPrefix {
        // TODO: currently this is just a wrapper over ICS024 (unimplemented).
        get_commitment_prefix()
    }

    fn fetch_client_consensus_state(
        &self,
        _client_id: &ClientId,
        _height: Height,
    ) -> Option<&dyn ConsensusState> {
        // Should call on a function that satisfies the ICS24 of getConsensusState().
        unimplemented!()
    }

    fn fetch_self_consensus_state(&self, _height: Height) -> Option<&dyn ConsensusState> {
        unimplemented!()
    }
}
