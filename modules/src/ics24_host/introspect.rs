use crate::ics23_commitment::CommitmentPrefix;
use crate::Height;

// TODO: The functions in this module are provisional. They should be implemented against a Chain.

/// Returns the current height of the local chain.
/// Satisfies the ICS024 requirement of getCurrentHeight().
pub fn current_height() -> Height {
    todo!()
}

/// Returns the trusting period (in number of block) for the local chain.
pub fn trusting_period() -> Height {
    todo!()
}

/// Returns the prefix that the local chain uses in the KV store.
/// Satisfies the ICS024 requirement of getCommitmentPrefix().
pub fn get_commitment_prefix() -> CommitmentPrefix {
    todo!()
}
