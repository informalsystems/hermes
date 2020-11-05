use thiserror::Error;

#[derive(Clone, Debug, Error)]
/// Chain errors
pub enum ChainError {
    #[error("failed")]
    Failed,

    #[error("requested proof for data in the privateStore")]
    NonProvableData,

    #[error("failed to send or receive through channel")]
    Channel,

    #[error("rpc client returned error: {0}")]
    RPC(String),

    #[error("invalid chain identifier format: {0}")]
    ChainIdentifier(String),

    #[error("the input header is not recognized as a header for this chain")]
    InvalidInputHeader,
}
