use crate::prelude::*;

use core::marker::{Send, Sync};

use dyn_clone::DynClone;
use erased_serde::Serialize as ErasedSerialize;
use ibc_proto::google::protobuf::Any;
use ibc_proto::protobuf::Protobuf as ErasedProtobuf;

use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::dynamic_typing::AsAny;
use crate::timestamp::Timestamp;

/// Abstract of consensus state information used by the validity predicate
/// to verify new commits & state roots.
///
/// Users are not expected to implement sealed::ErasedPartialEqConsensusState.
/// Effectively, that trait bound mandates implementors to derive PartialEq,
/// after which our blanket implementation will implement
/// `ErasedPartialEqConsensusState` for their type.
pub trait ConsensusState:
    AsAny
    + sealed::ErasedPartialEqConsensusState
    + DynClone
    + ErasedSerialize
    + ErasedProtobuf<Any, Error = Error>
    + core::fmt::Debug
    + Send
    + Sync
{
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// The timestamp of the consensus state
    fn timestamp(&self) -> Timestamp;

    /// Convert into a boxed trait object
    fn into_box(self) -> Box<dyn ConsensusState>
    where
        Self: Sized,
    {
        Box::new(self)
    }
}

// Implements `Clone` for `Box<dyn ConsensusState>`
dyn_clone::clone_trait_object!(ConsensusState);

// Implements `serde::Serialize` for all types that have ConsensusState as supertrait
erased_serde::serialize_trait_object!(ConsensusState);

pub fn downcast_consensus_state<CS: ConsensusState>(h: &dyn ConsensusState) -> Option<&CS> {
    h.as_any().downcast_ref::<CS>()
}

impl PartialEq for dyn ConsensusState {
    fn eq(&self, other: &Self) -> bool {
        self.eq_consensus_state(other)
    }
}

// see https://github.com/rust-lang/rust/issues/31740
impl PartialEq<&Self> for Box<dyn ConsensusState> {
    fn eq(&self, other: &&Self) -> bool {
        self.eq_consensus_state(other.as_ref())
    }
}

mod sealed {
    use super::*;

    pub trait ErasedPartialEqConsensusState {
        fn eq_consensus_state(&self, other: &dyn ConsensusState) -> bool;
    }

    impl<CS> ErasedPartialEqConsensusState for CS
    where
        CS: ConsensusState + PartialEq,
    {
        fn eq_consensus_state(&self, other: &dyn ConsensusState) -> bool {
            other
                .as_any()
                .downcast_ref::<CS>()
                .map_or(false, |h| self == h)
        }
    }
}
