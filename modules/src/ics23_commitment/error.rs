use flex_error::{define_error, DetailOnly};
use prost::DecodeError;

define_error! {
    #[derive(Debug, Clone)]
    Error {
        InvalidRawMerkleProof
        [ DetailOnly<DecodeError> ]
        |_| { "invalid raw merkle proof" },

        CommitmentProofDecodingFailed
        [ DetailOnly<DecodeError> ]
        |_| { "failed to decode commitment proof" },
    }
}
