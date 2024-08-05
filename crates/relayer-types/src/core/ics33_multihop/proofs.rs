use crate::Height;

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
// This struct stores the heights necessary for querying multihop channel proofs.
// The first/sending chain in a channel path has no preceding chain and need not be queried
// to check if it stores a consensus state for a previous chain. Hence, 'previous_chain_consensus_height`
// is an optional field.
pub struct MultihopProofHeights {
    // This is the height at which the proof(s) should be queried. Different chains along the
    // channel path require different types of proofs, all of which must be queried at this height.
    pub proof_query_height: Height,

    // If a proof for the consensus state of the previous chain in the channel path needs to be
    // obtained, it should prove the existence of the consensus state for 'previous_chain_consensus_height'.
    pub previous_chain_consensus_height: Option<Height>,
}

impl MultihopProofHeights {
    pub fn new(
        proof_query_height: Height,
        previous_chain_consensus_height: Option<Height>,
    ) -> Self {
        Self {
            proof_query_height,
            previous_chain_consensus_height,
        }
    }
}
