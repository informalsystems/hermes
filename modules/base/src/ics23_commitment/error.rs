use flex_error::{define_error, TraceError};
use prost::DecodeError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidRawMerkleProof
            [ TraceError<DecodeError> ]
            |_| { "invalid raw merkle proof" },

        CommitmentProofDecodingFailed
            [ TraceError<DecodeError> ]
            |_| { "failed to decode commitment proof" },

        EmptyCommitmentPrefix
            |_| { "empty commitment prefix" },

        EmptyMerkleProof
            |_| { "empty merkle proof" },

        EmptyMerkleRoot
            |_| { "empty merkle root" },

        EmptyVerifiedValue
            |_| { "empty verified value" },

        NumberOfSpecsMismatch
            |_| { "mismatch between the number of proofs with that of specs" },

        NumberOfKeysMismatch
            |_| { "mismatch between the number of proofs with that of keys" },

        InvalidMerkleProof
            |_| { "invalid merkle proof" },

        VerificationFailure
            |_| { "proof verification failed" }
    }
}
