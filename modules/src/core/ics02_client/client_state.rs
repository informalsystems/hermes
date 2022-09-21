use crate::{
	core::{ics02_client::client_def::ClientDef, ics24_host::identifier::ChainId},
	prelude::*,
	Height,
};
use core::{
	fmt::Debug,
	marker::{Send, Sync},
	time::Duration,
};
use alloc::string::String;

pub trait ClientState: Clone + Debug + Send + Sync {
	/// Client-specific options for upgrading the client
	type UpgradeOptions;
	type ClientDef: ClientDef<ClientState = Self>;

	/// Return the chain identifier which this client is serving (i.e., the client is verifying
	/// consensus states from this chain).
	fn chain_id(&self) -> ChainId;

	/// Type of client associated with this state (eg. Tendermint)
	fn client_def(&self) -> Self::ClientDef;

	/// Returns one of the prefixes that should be present in any client identifiers.
	/// The prefix is deterministic for a given chain type, hence all clients for a Tendermint-type
	/// chain, for example, will have the prefix '07-tendermint'.
	fn client_type(&self) -> ClientType;

	/// Latest height of consensus state
	fn latest_height(&self) -> Height;

	/// Freeze status of the client
	fn is_frozen(&self) -> bool {
		self.frozen_height().is_some()
	}

	/// Frozen height of the client
	fn frozen_height(&self) -> Option<Height>;

	/// Helper function to verify the upgrade client procedure.
	/// Resets all fields except the blockchain-specific ones,
	/// and updates the given fields.
	fn upgrade(
		self,
		upgrade_height: Height,
		upgrade_options: Self::UpgradeOptions,
		chain_id: ChainId,
	) -> Self;

	/// Helper function to verify the upgrade client procedure.
	fn expired(&self, elapsed: Duration) -> bool;

	/// Performs downcast of the client state from an "AnyClientState" type to T, otherwise
	/// panics. Downcast from `T` to `T` is always successful.
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

/// Type of the client, depending on the specific consensus algorithm.
pub type ClientType = String;
