use thiserror::Error;

#[derive(Clone, Debug, Error)]
/// Chain errors
pub enum ChainError {
    #[error("failed")]
    Failed,

    #[error("failed to send or receive through channel")]
    Channel,
}
