use flex_error::{define_error, TraceError};
use prost::DecodeError;

#[cfg(not(feature = "std"))]
impl crate::primitives::StdError for Error {}

define_error! {
    #[derive(Debug, Clone)]
    Error {
        InvalidRawMerkleProof
        [ TraceError<DecodeError> ]
        |_| { "invalid raw merkle proof" },

        CommitmentProofDecodingFailed
        [ TraceError<DecodeError> ]
        |_| { "failed to decode commitment proof" },
    }
}
