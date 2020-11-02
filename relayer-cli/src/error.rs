//! Error types

use anomaly::{BoxError, Context};
use thiserror::Error;

/// An error raised within the relayer CLI
pub type Error = anomaly::Error<Kind>;

/// Kinds of errors
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum Kind {
    /// Error in configuration file
    #[error("config error")]
    Config,

    /// Input/output error
    #[error("I/O error")]
    Io,

    /// Error during network query
    #[error("query error")]
    Query,

    /// Error during transaction submission
    #[error("tx error")]
    Tx,

    /// Error during transaction submission
    #[error("keys error")]
    Keys,
}

impl Kind {
    /// Create an error context from this error
    pub fn context(self, source: impl Into<BoxError>) -> Context<Kind> {
        Context::new(self, Some(source.into()))
    }
}
