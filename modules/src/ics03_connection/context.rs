//! ICS3 (connection) context. The two traits `ConnectionReader` and `ConnectionKeeper` define
//! the interface that any host chain must implement to be able to process any `ConnectionMsg`.
//! See "ADR 003: IBC protocol implementation" for more details.

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics03_connection::connection::{ConnectionEnd, State};
use crate::ics03_connection::error::Error;
use crate::ics03_connection::handler::ConnectionResult;
use crate::ics03_connection::version::{get_compatible_versions, pick_version, Version};
use crate::ics23_commitment::commitment::CommitmentPrefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

/// A context supplying all the necessary read-only dependencies for processing any `ConnectionMsg`.
pub trait ConnectionReader {
    /// Returns the ConnectionEnd for the given identifier `conn_id`.
    fn connection_end(&self, conn_id: &ConnectionId) -> Option<ConnectionEnd>;

    /// Returns the ClientState for the given identifier `client_id`.
    fn client_state(&self, client_id: &ClientId) -> Option<AnyClientState>;

    /// Returns the current height of the local chain.
    fn host_current_height(&self) -> Height;

    /// Returns the number of consensus state entries that the local chain maintains. The history
    /// size determines the pruning window of the host chain.
    fn host_chain_history_size(&self) -> usize;

    /// Returns the prefix that the local chain uses in the KV store.
    fn commitment_prefix(&self) -> CommitmentPrefix;

    /// Returns the ConsensusState that the given client stores at a specific height.
    fn client_consensus_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Option<AnyConsensusState>;

    /// Returns the ConsensusState of the host (local) chain at a specific height.
    fn host_consensus_state(&self, height: Height) -> Option<AnyConsensusState>;

    /// Function required by ICS 03. Returns the list of all possible versions that the connection
    /// handshake protocol supports.
    fn get_compatible_versions(&self) -> Vec<Version> {
        get_compatible_versions()
    }

    /// Function required by ICS 03. Returns one version out of the supplied list of versions, which the
    /// connection handshake protocol prefers.
    fn pick_version(
        &self,
        supported_versions: Vec<Version>,
        counterparty_candidate_versions: Vec<Version>,
    ) -> Option<Version> {
        pick_version(supported_versions, counterparty_candidate_versions)
    }
}

/// A context supplying all the necessary write-only dependencies (i.e., storage writing facility)
/// for processing any `ConnectionMsg`.
pub trait ConnectionKeeper {
    fn store_connection_result(&mut self, result: ConnectionResult) -> Result<(), Error> {
        match result.connection_end.state() {
            State::Init => {
                let connection_id = self.next_connection_id();
                self.store_connection(&connection_id, &result.connection_end)?;
                // If this is the first time the handler processed this connection, associate the
                // connection end to its client identifier.
                self.store_connection_to_client(
                    &connection_id,
                    &result.connection_end.client_id(),
                )?;
            }
            State::TryOpen => {
                self.store_connection(
                    &result.connection_id.clone().unwrap(),
                    &result.connection_end,
                )?;
                // If this is the first time the handler processed this connection, associate the
                // connection end to its client identifier.
                self.store_connection_to_client(
                    &result.connection_id.clone().unwrap(),
                    &result.connection_end.client_id(),
                )?;
            }
            _ => {
                self.store_connection(&result.connection_id.unwrap(), &result.connection_end)?;
            }
        }
        Ok(())
    }

    fn next_connection_id(&mut self) -> ConnectionId;

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
