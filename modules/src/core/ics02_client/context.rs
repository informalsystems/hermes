//! ICS2 (client) context. The two traits `ClientReader` and `ClientKeeper` define the interface
//! that any host chain must implement to be able to process any `ClientMsg`. See
//! "ADR 003: IBC protocol implementation" for more details.

use crate::{
	core::{
		ics02_client::{
			client_consensus::ConsensusState,
			client_def::{ClientDef, ConsensusUpdateResult},
			client_message::ClientMessage,
			client_state::{ClientState, ClientType},
			error::{Error, ErrorDetail},
			handler::ClientResult::{self, Create, Update, Upgrade},
		},
		ics24_host::identifier::ClientId,
	},
	timestamp::Timestamp,
	Height,
};
use alloc::{string::String, vec::Vec};
use core::fmt::Debug;

/// Defines the read-only part of ICS2 (client functions) context.
pub trait ClientReader: ClientKeeper {
	fn client_type(&self, client_id: &ClientId) -> Result<ClientType, Error>;
	fn client_state(&self, client_id: &ClientId) -> Result<Self::AnyClientState, Error>;

	/// Retrieve the consensus state for the given client ID at the specified
	/// height.
	///
	/// Returns an error if no such state exists.
	fn consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Self::AnyConsensusState, Error>;

	/// This should return the host type.
	fn host_client_type(&self) -> String;

	/// Similar to `consensus_state`, attempt to retrieve the consensus state,
	/// but return `None` if no state exists at the given height.
	fn maybe_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Option<Self::AnyConsensusState>, Error> {
		match self.consensus_state(client_id, height) {
			Ok(cs) => Ok(Some(cs)),
			Err(e) => match e.detail() {
				ErrorDetail::ConsensusStateNotFound(_) => Ok(None),
				_ => Err(e),
			},
		}
	}

	/// Search for the lowest consensus state higher than `height`.
	fn next_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Option<Self::AnyConsensusState>, Error>;

	/// Search for the highest consensus state lower than `height`.
	fn prev_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Option<Self::AnyConsensusState>, Error>;

	/// Returns the current height of the local chain.
	fn host_height(&self) -> Height;

	/// Returns the current timestamp of the local chain.
	fn host_timestamp(&self) -> Timestamp;

	/// Returns the `ConsensusState` of the host (local) chain at a specific height.
	/// If this is fetched from a proof whose origin is off-chain, it should ideally be verified
	/// first.
	fn host_consensus_state(
		&self,
		height: Height,
		proof: Option<Vec<u8>>,
	) -> Result<Self::AnyConsensusState, Error>;

	/// Returns a natural number, counting how many clients have been created thus far.
	/// The value of this counter should increase only via method
	/// `ClientKeeper::increase_client_counter`.
	fn client_counter(&self) -> Result<u64, Error>;
}

pub trait ClientTypes: 'static {
	type AnyClientMessage: ClientMessage;
	type AnyClientState: ClientState<ClientDef = Self::ClientDef> + Eq;
	type AnyConsensusState: ConsensusState + Eq + 'static;

	/// Client definition type (used for verification)
	type ClientDef: ClientDef<
		ClientMessage = Self::AnyClientMessage,
		ClientState = Self::AnyClientState,
		ConsensusState = Self::AnyConsensusState,
	>;
}

/// Defines the write-only part of ICS2 (client functions) context.
pub trait ClientKeeper: ClientTypes
where
	Self: Clone + Debug + Eq,
{
	fn store_client_result(&mut self, handler_res: ClientResult<Self>) -> Result<(), Error> {
		match handler_res {
			Create(res) => {
				let client_id = res.client_id.clone();

				self.store_client_type(client_id.clone(), res.client_type)?;
				self.store_client_state(client_id.clone(), res.client_state.clone())?;
				self.store_consensus_state(
					client_id,
					res.client_state.latest_height(),
					res.consensus_state,
				)?;
				self.increase_client_counter();
				self.store_update_time(
					res.client_id.clone(),
					res.client_state.latest_height(),
					res.processed_time,
				)?;
				self.store_update_height(
					res.client_id,
					res.client_state.latest_height(),
					res.processed_height,
				)?;
				Ok(())
			},
			Update(res) => {
				self.store_client_state(res.client_id.clone(), res.client_state.clone())?;
				match res.consensus_state {
					None => {},
					Some(cs_state_update) => match cs_state_update {
						ConsensusUpdateResult::Single(cs_state) => {
							self.store_consensus_state(
								res.client_id.clone(),
								res.client_state.latest_height(),
								cs_state,
							)?;

							self.store_update_time(
								res.client_id.clone(),
								res.client_state.latest_height(),
								res.processed_time,
							)?;
							self.store_update_height(
								res.client_id,
								res.client_state.latest_height(),
								res.processed_height,
							)?;
						},
						ConsensusUpdateResult::Batch(cs_states) => {
							for (height, cs_state) in cs_states {
								self.store_consensus_state(
									res.client_id.clone(),
									height,
									cs_state,
								)?;
								self.store_update_time(
									res.client_id.clone(),
									height,
									res.processed_time,
								)?;
								self.store_update_height(
									res.client_id.clone(),
									height,
									res.processed_height,
								)?;
							}
						},
					},
				}
				Ok(())
			},
			Upgrade(res) => {
				self.store_client_state(res.client_id.clone(), res.client_state.clone())?;
				match res.consensus_state {
					None => {},
					Some(cs_state_update) => match cs_state_update {
						ConsensusUpdateResult::Single(cs_state) => {
							self.store_consensus_state(
								res.client_id.clone(),
								res.client_state.latest_height(),
								cs_state,
							)?;
						},
						ConsensusUpdateResult::Batch(cs_states) => {
							for (height, cs_state) in cs_states {
								self.store_consensus_state(
									res.client_id.clone(),
									height,
									cs_state,
								)?;
							}
						},
					},
				}
				Ok(())
			},
		}
	}

	/// Called upon successful client creation
	fn store_client_type(
		&mut self,
		client_id: ClientId,
		client_type: ClientType,
	) -> Result<(), Error>;

	/// Called upon successful client creation and update
	fn store_client_state(
		&mut self,
		client_id: ClientId,
		client_state: Self::AnyClientState,
	) -> Result<(), Error>;

	/// Called upon successful client creation and update
	fn store_consensus_state(
		&mut self,
		client_id: ClientId,
		height: Height,
		consensus_state: Self::AnyConsensusState,
	) -> Result<(), Error>;

	/// Called upon client creation.
	/// Increases the counter which keeps track of how many clients have been created.
	/// Should never fail.
	fn increase_client_counter(&mut self);

	/// Called upon successful client update.
	/// Implementations are expected to use this to record the specified time as the time at which
	/// this update (or header) was processed.
	fn store_update_time(
		&mut self,
		client_id: ClientId,
		height: Height,
		timestamp: Timestamp,
	) -> Result<(), Error>;

	/// Called upon successful client update.
	/// Implementations are expected to use this to record the specified height as the height at
	/// at which this update (or header) was processed.
	fn store_update_height(
		&mut self,
		client_id: ClientId,
		height: Height,
		host_height: Height,
	) -> Result<(), Error>;

	/// validates the client parameters for a client of the running chain
	/// This function is only used to validate the client state the counterparty stores for this
	/// chain
	fn validate_self_client(&self, client_state: &Self::AnyClientState) -> Result<(), Error>;
}
