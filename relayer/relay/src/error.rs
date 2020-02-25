//! This module defines the various errors that be raised in the relayer.

use anomaly::{BoxError, Context};
use thiserror::Error;

/// An error that can be raised by the relayer.
pub type Error = anomaly::Error<Kind>;

/// Various kinds of errors that can be raiser by the relayer.
#[derive(Clone, Debug, Error)]
pub enum Kind {
    /// I/O error
    #[error("I/O error")]
    ConfigIo,

    /// Invalid configuration
    #[error("invalid configuration")]
    Config,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
