use crate::context::SelfChainType;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics03_connection::connection::{ConnectionEnd, State};
use crate::ics03_connection::error::Error;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use tendermint::block::Height;

/// A context supplying all the necessary read-only dependencies for processing any `ICS3Msg`.
pub trait ConnectionReader {
    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn fetch_connection_end(&self, conn_id: &ConnectionId) -> Option<&ConnectionEnd>;

    /// Returns the ClientState for the given identifier `client_id`.
    fn fetch_client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;

    /// Returns the current height of the local chain.
    fn chain_current_height(&self) -> Height;

    /// Returns the number of consensus state historical entries for the local chain.
    fn chain_consensus_states_history_size(&self) -> usize;

    fn chain_type(&self) -> SelfChainType;

    /// Returns the prefix that the local chain uses in the KV store.
    fn commitment_prefix(&self) -> CommitmentPrefix;

    /// Returns the ConsensusState that the given client stores at a specific height.
    fn fetch_client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState>;

    /// Returns the ConsensusState of the local chain at a specific height.
    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState>;

    /// Function required by ICS 03. Returns the list of all possible versions that the connection
    /// handshake protocol supports.
    fn get_compatible_versions(&self) -> Vec<String>;

    /// Function required by ICS 03. Returns one version out of the supplied list of versions, which the
    /// connection handshake protocol prefers.
    fn pick_version(&self, counterparty_candidate_versions: Vec<String>) -> String;
}

/// A context supplying all the necessary write-only dependencies (i.e., storage functionalities)
/// for processing any `ICS3Msg`.
pub trait ConnectionKeeper {
    fn store_connection_result(&mut self, result: ConnectionResult) -> Result<(), Error> {
        match result.connection_end.state() {
            State::Init | State::TryOpen => {
                self.store_connection(&result.connection_id, &result.connection_end)?;
                // If this is the first time the handler processed this connection, associate the
                // connection end to its client identifier.
                self.store_connection_to_client(
                    &result.connection_id,
                    &result.connection_end.client_id(),
                )?;
            }
            _ => {
                self.store_connection(&result.connection_id, &result.connection_end)?;
            }
        }
        Ok(())
    }

    /// Stores the given connection_end at a path associated with the connection_id.
    fn store_connection(
        &mut self,
        connection_id: &ConnectionId,
        connection_end: &ConnectionEnd,
    ) -> Result<(), Error>;

    /// Stores the given connection_id at a path associated with the client_id.
    fn store_connection_to_client(
        &mut self,
        connection_id: &ConnectionId,
        client_id: &ClientId,
    ) -> Result<(), Error>;
}
