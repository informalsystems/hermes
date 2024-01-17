use core::{
    fmt::Debug,
    marker::{
        Send,
        Sync,
    },
};

use crate::{
    core::{
        ics02_client::client_type::ClientType,
        ics23_commitment::commitment::CommitmentRoot,
    },
    timestamp::Timestamp,
};

/// Abstract of consensus state information used by the validity predicate
/// to verify new commits & state roots.
///
/// Users are not expected to implement sealed::ErasedPartialEqConsensusState.
/// Effectively, that trait bound mandates implementers to derive PartialEq,
/// after which our blanket implementation will implement
/// `ErasedPartialEqConsensusState` for their type.
pub trait ConsensusState: Clone + Debug + Send + Sync // Any: From<Self>,
{
    /// Type of client associated with this consensus state (eg. Tendermint)
    fn client_type(&self) -> ClientType;

    /// Commitment root of the consensus state, which is used for key-value pair verification.
    fn root(&self) -> &CommitmentRoot;

    /// The timestamp of the consensus state
    fn timestamp(&self) -> Timestamp;
}
