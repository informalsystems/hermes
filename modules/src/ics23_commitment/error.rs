use prost::DecodeError;
use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Error {
    #[error("invalid raw merkle proof")]
    InvalidRawMerkleProof(DecodeError),

    #[error("failed to decode commitment proof")]
    CommitmentProofDecodingFailed(DecodeError),
}
