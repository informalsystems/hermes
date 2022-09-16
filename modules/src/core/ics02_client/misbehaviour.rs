use crate::{core::ics24_host::identifier::ClientId, prelude::*, Height};

pub trait Misbehaviour: Clone + core::fmt::Debug + Send + Sync {
	/// The type of client (eg. Tendermint)
	fn client_id(&self) -> &ClientId;

	/// The height of the consensus state
	fn height(&self) -> Height;

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
