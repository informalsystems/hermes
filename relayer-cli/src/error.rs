//! Error types

use anomaly::{BoxError, Context};
use ibc_relayer::error::Kind as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer::util::retry::RetryableError;
use thiserror::Error;

/// An error raised within the relayer CLI
pub type Error = anomaly::Error<Kind>;

/// Kinds of errors
#[derive(Clone, Debug, Error)]
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

    /// Error while spawning the runtime
    #[error("chain runtime error")]
    Runtime,

    /// Error during transaction submission
    #[error("tx error")]
    Tx,

    /// Error during transaction submission
    #[error("keys error")]
    Keys,

    /// Fatal error
    #[error("fatal error")]
    Fatal,

    /// Error from relayer
    #[error("relayer error")]
    Relayer(RelayerError),

    /// Error from foreign client
    #[error("foreign client error")]
    ForeignClient(ForeignClientError),
}

impl RetryableError for Kind {
    #[allow(clippy::match_like_matches_macro)]
    fn is_retryable(&self) -> bool {
        match self {
            Kind::Io => true,
            Kind::Fatal => false,
            Kind::Config => false,
            Kind::Relayer(e) => e.is_retryable(),
            Kind::ForeignClient(e) => e.is_retryable(),

            // TODO: actually classify the remaining variants on whether they are retryable
            _ => true,
        }
    }
}

impl Kind {
    /// Create an error context from this error
    pub fn context(self, source: impl Into<BoxError>) -> Context<Kind> {
        Context::new(self, Some(source.into()))
    }
}
