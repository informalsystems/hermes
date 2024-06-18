use flex_error::{define_error, TraceError};
use prost::EncodeError;
use serde::Serialize;

use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::Height;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    ProofError {
        ZeroHeight
            | _ | { format_args!("proof height cannot be zero") },

        EmptyProof
            | _ | { format_args!("proof cannot be empty") },

        Encode
            [ TraceError<EncodeError> ]
            | _ | { "protobuf encode error" },
    }
}

/// Structure comprising proofs in a message. Proofs are typically present in messages for
/// handshake protocols, e.g., ICS3 connection (open) handshake or ICS4 channel (open and close)
/// handshake, as well as for ICS4 packets, timeouts, and acknowledgements.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Proofs {
    object_proof: CommitmentProofBytes,
    client_proof: Option<CommitmentProofBytes>,
    consensus_proof: Option<ConsensusProof>,
    host_consensus_state_proof: Option<CommitmentProofBytes>,
    /// Currently used for proof_close for MsgTimeoutOnCLose where object_proof is proof_unreceived
    other_proof: Option<CommitmentProofBytes>,
    /// Height for the commitment root for proving the proofs above.
    /// When creating these proofs, the chain is queried at `height-1`.
    height: Height,
}

impl Proofs {
    pub fn new(
        object_proof: CommitmentProofBytes,
        client_proof: Option<CommitmentProofBytes>,
        consensus_proof: Option<ConsensusProof>,
        host_consensus_state_proof: Option<CommitmentProofBytes>,
        other_proof: Option<CommitmentProofBytes>,
        height: Height,
    ) -> Result<Self, ProofError> {
        Ok(Self {
            object_proof,
            client_proof,
            consensus_proof,
            host_consensus_state_proof,
            other_proof,
            height,
        })
    }

    /// Getter for the consensus_proof field of this proof. Intuitively, this is a proof that a
    /// client on the source chain stores a consensus state for the destination chain.
    pub fn consensus_proof(&self) -> Option<&ConsensusProof> {
        self.consensus_proof.as_ref()
    }

    /// Getter for the host_consensus_state_proof field of this proof.
    /// This is an optional proof data for host state machines that are unable to introspect their own consensus state.
    pub fn host_consensus_state_proof(&self) -> Option<&CommitmentProofBytes> {
        self.host_consensus_state_proof.as_ref()
    }

    /// Getter for the height field of this proof (i.e., the consensus height where this proof was
    /// created).
    pub fn height(&self) -> Height {
        self.height
    }

    /// Getter for the object-specific proof (e.g., proof for connection state or channel state).
    pub fn object_proof(&self) -> &CommitmentProofBytes {
        &self.object_proof
    }

    /// Getter for the client_proof.
    pub fn client_proof(&self) -> Option<&CommitmentProofBytes> {
        self.client_proof.as_ref()
    }

    /// Getter for the other_proof.
    pub fn other_proof(&self) -> Option<&CommitmentProofBytes> {
        self.other_proof.as_ref()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConsensusProof {
    proof: CommitmentProofBytes,
    height: Height,
}

impl ConsensusProof {
    pub fn new(
        consensus_proof: CommitmentProofBytes,
        consensus_height: Height,
    ) -> Result<Self, ProofError> {
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
    pub fn proof(&self) -> &CommitmentProofBytes {
        &self.proof
    }
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
// This struct stores the heights necessary for querying multihop channel proofs.
// The first/sending chain in a channel path has no preceding chain and need not be queried
// to check if it stores a consensus state for a previous chain. Hence, 'consensus_height` is
// an optional field.
pub struct MultihopProofHeights {
    // This is the height at which the proof(s) should be queried. Different chains along the
    // channel path require different types of proofs, all of which must be queried at this height.
    pub query_height: Height,
    // If a consensus state proof needs to be queried, it should be queried at 'proof_height'
    // and needs to prove the existence of the consensus state for height 'consensus_height'.
    pub consensus_height: Option<Height>,
}

impl MultihopProofHeights {
    pub fn new(query_height: Height, consensus_height: Option<Height>) -> Self {
        Self {
            query_height,
            consensus_height,
        }
    }
}
