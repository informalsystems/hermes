use std::marker::{Send, Sync};
use std::time::Duration;

use dyn_clone::DynClone;
use erased_serde::Serialize as ErasedSerialize;
use ibc_proto::google::protobuf::Any;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics24_host::identifier::ChainId;
use crate::dynamic_typing::AsAny;

use crate::Height;

use super::consensus_state::ConsensusState;

pub trait ClientState:
    AsAny
    + sealed::ErasedPartialEqClientState
    + DynClone
    + ErasedSerialize
    + ErasedProtobuf<Any, Error = Error>
    + core::fmt::Debug
    + Send
    + Sync
{
    /// Return the chain identifier which this client is serving (i.e., the client is verifying
    /// consensus states from this chain).
    fn chain_id(&self) -> ChainId;

    /// Type of client associated with this state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Latest height the client was updated to
    fn latest_height(&self) -> Height;

    /// Freeze status of the client
    fn is_frozen(&self) -> bool {
        self.frozen_height().is_some()
    }

    /// Frozen height of the client
    fn frozen_height(&self) -> Option<Height>;

    /// Check if the state is expired when `elapsed` time has passed since the latest consensus
    /// state timestamp
    fn expired(&self, elapsed: Duration) -> bool;

    /// Helper function to verify the upgrade client procedure.
    /// Resets all fields except the blockchain-specific ones,
    /// and updates the given fields.
    fn upgrade(
        &mut self,
        upgrade_height: Height,
        upgrade_options: &dyn UpgradeOptions,
        chain_id: ChainId,
    );

    /// Convert into a boxed trait object
    fn into_box(self) -> Box<dyn ClientState>
    where
        Self: Sized,
    {
        Box::new(self)
    }
}

// Implements `Clone` for `Box<dyn ClientState>`
dyn_clone::clone_trait_object!(ClientState);

// Implements `serde::Serialize` for all types that have ClientState as supertrait
erased_serde::serialize_trait_object!(ClientState);

impl PartialEq for dyn ClientState {
    fn eq(&self, other: &Self) -> bool {
        self.eq_client_state(other)
    }
}

// see https://github.com/rust-lang/rust/issues/31740
impl PartialEq<&Self> for Box<dyn ClientState> {
    fn eq(&self, other: &&Self) -> bool {
        self.eq_client_state(other.as_ref())
    }
}

pub fn downcast_client_state<CS: ClientState>(h: &dyn ClientState) -> Option<&CS> {
    h.as_any().downcast_ref::<CS>()
}

pub trait UpgradeOptions: AsAny {}

pub struct UpdatedState {
    pub client_state: Box<dyn ClientState>,
    pub consensus_state: Box<dyn ConsensusState>,
}

mod sealed {
    use super::*;

    pub trait ErasedPartialEqClientState {
        fn eq_client_state(&self, other: &dyn ClientState) -> bool;
    }

    impl<CS> ErasedPartialEqClientState for CS
    where
        CS: ClientState + PartialEq,
    {
        fn eq_client_state(&self, other: &dyn ClientState) -> bool {
            other
                .as_any()
                .downcast_ref::<CS>()
                .map_or(false, |h| self == h)
        }
    }
}
