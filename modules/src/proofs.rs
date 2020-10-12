use crate::ics23_commitment::commitment::CommitmentProof;
use crate::Height;
use ibc_proto::ibc::client::Height as RawHeight;
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
        proof_height: ibc_proto::ibc::client::Height,
    ) -> Result<Self, String> {
        let height: Height = proof_height
            .try_into()
            .map_err(|_| "error parsing proof height")?;

        if height.is_zero() {
            return Err("Proofs height cannot be zero".to_string());
        }

        if object_proof.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            object_proof,
            client_proof,
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
    pub fn new(
        consensus_proof: CommitmentProof,
        consensus_height_raw: RawHeight,
    ) -> Result<Self, String> {
        let consensus_height: Height = consensus_height_raw
            .try_into()
            .map_err(|_| "cannot parse consensus height")?;

        if consensus_height.is_zero() {
            return Err("Consensus height cannot be zero".to_string());
        }
        if consensus_proof.is_empty() {
            return Err("Proof cannot be empty".to_string());
        }

        Ok(Self {
            proof: consensus_proof,
            height: consensus_height,
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
