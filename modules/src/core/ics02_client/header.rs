use crate::{prelude::*, Height};

/// Abstract of consensus state update information
pub trait Header: Clone + core::fmt::Debug + Send + Sync {
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

	/// The height of the header
	fn height(&self) -> Height;
}
