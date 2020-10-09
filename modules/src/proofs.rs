use crate::ics23_commitment::commitment::CommitmentProof;
use tendermint::block::Height;

use serde_derive::{Deserialize, Serialize};
use std::convert::TryInto;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Proofs {
    object_proof: CommitmentProof,
    client_proof: Option<CommitmentProof>,
    consensus_proof: Option<ConsensusProof>,
    /// Height for both the above proofs
    height: Height,
}

impl Proofs {
    pub fn new(
        object_proof: CommitmentProof,
        client_proof: Option<CommitmentProof>,
        consensus_proof: Option<ConsensusProof>,
        height: u64,
    ) -> Result<Self, String> {
        if height == 0 {
            return Err("Proofs height cannot be zero".to_string());
        }

        if object_proof.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            object_proof,
            client_proof,
            consensus_proof,
            height: height.try_into().unwrap(),
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

    /// Getter for the client_proof
    pub fn client_proof(&self) -> &Option<CommitmentProof> {
        &self.client_proof
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConsensusProof {
    proof: CommitmentProof,
    height: Height,
}

impl ConsensusProof {
    pub fn new(consensus_proof: CommitmentProof, consensus_height: u64) -> Result<Self, String> {
        if consensus_height == 0 {
            return Err("Consensus height cannot be zero".to_string());
        }
        if consensus_proof.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            proof: consensus_proof,
            height: consensus_height.try_into().unwrap(), // FIXME: unwrap
        })
    }

    /// Getter for the height field of this consensus proof.
    pub fn height(&self) -> Height {
        self.height
    }

    /// Getter for the proof (CommitmentProof) field of this consensus proof.
    pub fn proof(&self) -> &CommitmentProof {
        &self.proof
    }
}
