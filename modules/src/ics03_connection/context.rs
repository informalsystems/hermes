use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics03_connection::error::Error;
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

/// A context supplying all the necessary dependencies for processing any `ICS3Msg`.
pub trait ConnectionReader {
    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn fetch_connection_end(&self, conn_id: &ConnectionId) -> Option<&ConnectionEnd>;

    /// Returns the ClientState for the given identifier `client_id`.
    fn fetch_client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;

    /// Returns the current height of the local chain.
    fn chain_current_height(&self) -> Height;

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> usize;

    /// Returns the prefix that the local chain uses in the KV store.
    fn commitment_prefix(&self) -> CommitmentPrefix;

    /// Returns the ConsensusState of the local chain at a specific height.
    fn fetch_client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState>;

    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState>;
}

pub trait ConnectionKeeper {
    fn store_connection(
        &mut self,
        connection_id: ConnectionId,
        connection_end: ConnectionEnd,
    ) -> Result<(), Error>;
}
