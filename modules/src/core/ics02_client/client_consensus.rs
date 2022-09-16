use crate::{
	core::{ics23_commitment::commitment::CommitmentRoot, ics24_host::identifier::ClientId},
	events::WithBlockDataType,
	prelude::*,
	timestamp::Timestamp,
};
use core::{
	fmt::Debug,
	marker::{Send, Sync},
};

pub trait ConsensusState: Clone + Debug + Send + Sync {
	type Error;

	/// Commitment root of the consensus state, which is used for key-value pair verification.
	fn root(&self) -> &CommitmentRoot;

	/// Returns the timestamp of the state.
	fn timestamp(&self) -> Timestamp;

	fn downcast<T: Clone + 'static>(self) -> Option<T>
	where
		Self: 'static,
	{
		<dyn core::any::Any>::downcast_ref(&self).cloned()
	}

	fn wrap(sub_state: &dyn core::any::Any) -> Option<Self>
	where
		Self: 'static,
	{
		sub_state.downcast_ref::<Self>().cloned()
	}

	fn encode_to_vec(&self) -> Vec<u8>;
}

/// Query request for a single client event, identified by `event_id`, for `client_id`.
#[derive(Clone, Debug)]
pub struct QueryClientEventRequest {
	pub height: crate::Height,
	pub event_id: WithBlockDataType,
	pub client_id: ClientId,
	pub consensus_height: crate::Height,
}
