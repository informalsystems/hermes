use crate::ics23_commitment::CommitmentProof;
use crate::Height;
use serde_derive::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proofs {
    object_proof: CommitmentProof,
    consensus_proof: Option<ConsensusProof>,
    /// Height for both the above proofs
    height: Height,
}

impl Proofs {
    pub fn new(
        object_proof: CommitmentProof,
        consensus_proof: Option<ConsensusProof>,
        height: u64,
    ) -> Result<Self, String> {
        if height == 0 {
            return Err("Proofs height cannot be zero".to_string());
        }

        if object_proof.ops.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            object_proof,
            consensus_proof,
            height,
        })
    }

    /// Getter for the consensus_proof field of this proof.
    pub fn consensus_proof(&self) -> Option<ConsensusProof> {
        self.consensus_proof.clone()
    }

    /// Getter for the height field of this proof (i.e., the consensus height where this proof was
    /// created).
    pub fn height(&self) -> Height {
        self.height
    }

    /// Getter for the object-specific proof (e.g., proof for connection state or channel state).
    pub fn object_proof(&self) -> &CommitmentProof {
        &self.object_proof
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsensusProof {
    pub consensus_proof: CommitmentProof,
    pub consensus_height: Height,
}

impl ConsensusProof {
    pub fn new(consensus_proof: CommitmentProof, consensus_height: u64) -> Result<Self, String> {
        if consensus_height == 0 {
            return Err("Consensus height cannot be zero".to_string());
        }
        if consensus_proof.ops.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            consensus_proof,
            consensus_height,
        })
    }

    /// Getter for the consensus_height field of this consensus proof.
    pub fn consensus_height(&self) -> Height {
        self.consensus_height
    }
}
