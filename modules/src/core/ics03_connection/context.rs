//! ICS3 (connection) context. The two traits `ConnectionReader` and `ConnectionKeeper` define
//! the interface that any host chain must implement to be able to process any `ConnectionMsg`.
//! See "ADR 003: IBC protocol implementation" for more details.

use crate::{
	core::{
		ics03_connection::{
			connection::ConnectionEnd,
			error::Error,
			handler::{ConnectionIdState, ConnectionResult},
			version::{get_compatible_versions, pick_version, Version},
		},
		ics23_commitment::commitment::CommitmentPrefix,
		ics24_host::identifier::{ClientId, ConnectionId},
	},
	prelude::*,
	Height,
};

/// A context supplying all the necessary read-only dependencies for processing any `ConnectionMsg`.
pub trait ConnectionReader {
	/// Returns the ConnectionEnd for the given identifier `conn_id`.
	fn connection_end(&self, conn_id: &ConnectionId) -> Result<ConnectionEnd, Error>;

	/// Returns the oldest height available on the local chain.
	fn host_oldest_height(&self) -> Height;

	/// Returns the prefix that the local chain uses in the KV store.
	fn commitment_prefix(&self) -> CommitmentPrefix;

	/// Function required by ICS 03. Returns the list of all possible versions that the connection
	/// handshake protocol supports.
	fn get_compatible_versions(&self) -> Vec<Version> {
		get_compatible_versions()
	}

	/// Function required by ICS 03. Returns one version out of the supplied list of versions, which
	/// the connection handshake protocol prefers.
	fn pick_version(
		&self,
		supported_versions: Vec<Version>,
		counterparty_candidate_versions: Vec<Version>,
	) -> Result<Version, Error> {
		pick_version(supported_versions, counterparty_candidate_versions)
	}

	/// Returns a counter on how many connections have been created thus far.
	/// The value of this counter should increase only via method
	/// `ConnectionKeeper::increase_connection_counter`.
	fn connection_counter(&self) -> Result<u64, Error>;
}

/// A context supplying all the necessary write-only dependencies (i.e., storage writing facility)
/// for processing any `ConnectionMsg`.
pub trait ConnectionKeeper {
	fn store_connection_result(&mut self, result: ConnectionResult) -> Result<(), Error> {
		self.store_connection(result.connection_id.clone(), &result.connection_end)?;

		// If we generated an identifier, increase the counter & associate this new identifier
		// with the client id.
		if matches!(result.connection_id_state, ConnectionIdState::Generated) {
			self.increase_connection_counter();

			// Also associate the connection end to its client identifier.
			self.store_connection_to_client(
				result.connection_id.clone(),
				result.connection_end.client_id(),
			)?;
		}

		Ok(())
	}

	/// Stores the given connection_end at a path associated with the connection_id.
	fn store_connection(
		&mut self,
		connection_id: ConnectionId,
		connection_end: &ConnectionEnd,
	) -> Result<(), Error>;

	/// Stores the given connection_id at a path associated with the client_id.
	fn store_connection_to_client(
		&mut self,
		connection_id: ConnectionId,
		client_id: &ClientId,
	) -> Result<(), Error>;

	/// Called upon connection identifier creation (Init or Try process).
	/// Increases the counter which keeps track of how many connections have been created.
	/// Should never fail.
	fn increase_connection_counter(&mut self);
}
