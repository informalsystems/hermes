use crate::ics23_commitment::CommitmentPrefix;
use crate::Height;

// TODO: The functions in this module are provisional. They should be implemented against a Chain.

/// Returns the current height of the local chain.
/// Satisfies the ICS024 requirement of getCurrentHeight().
pub fn current_height() -> Height {
    todo!()
}

/// Returns the number of local consensus states available for the local chain.
pub fn get_consensus_state_history_size() -> u32 {
    todo!()
}

/// Returns the prefix that the local chain uses in the KV store.
/// Satisfies the ICS024 requirement of getCommitmentPrefix().
pub fn get_commitment_prefix() -> CommitmentPrefix {
    todo!()
}
