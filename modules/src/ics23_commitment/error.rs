use prost::DecodeError;
use flex_error::*;

define_error! {
    Error {
        InvalidRawMerkleProof
        [ DisplayError<DecodeError> ]
        |_| { "invalid raw merkle proof" },

        CommitmentProofDecodingFailed
        [ DisplayError<DecodeError> ]
        |_| { "failed to decode commitment proof" },
    }
}