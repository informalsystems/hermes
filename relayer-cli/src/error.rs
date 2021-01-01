//! Error types for CLIs

use anomaly::{BoxError, Context};
use thiserror::Error;

/// An error raised within the relayer CLI
pub type Error = anomaly::Error<Kind>;

/// Kinds of errors
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum ErrorMsg {
    /// Error during relayer network query
    #[error("query error")]
    Query,

    /// Error during relayer transaction submission
    #[error("tx error")]
    Tx,
}

/// Kinds of errors
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum Kind {
    /// Error during relayer network query
    #[error("query error")]
    Query,

    /// Error during relayer transaction submission
    #[error("tx error")]
    Tx,

    /// Error during relayer key manipulation
    #[error("keys error")]
    Keys,
}

impl Kind {
    /// Create an error context from this error
    pub fn context(self, source: impl Into<BoxError>) -> Context<Kind> {
        Context::new(self, Some(source.into()))
    }
}
