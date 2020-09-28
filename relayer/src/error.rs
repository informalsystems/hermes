//! This module defines the various errors that be raised in the relayer.

use anomaly::{BoxError, Context};
use ibc::ics24_host::identifier::ClientId;
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
    #[error("Invalid configuration")]
    Config,

    /// RPC error (typically raised by the RPC client or the RPC requester)
    #[error("RPC error")]
    Rpc,

    /// Light client error, typically raised by a `Client`
    #[error("Light client error")]
    LightClient,

    /// Trusted store error, raised by instances of `Store`
    #[error("Store error")]
    Store,

    /// Event error (raised by the event monitor)
    #[error("Bad Notification")]
    Event,

    /// Response parsing error
    #[error("Could not parse/unmarshall response")]
    ResponseParsing,

    /// Response does not contain data
    #[error("Empty response value")]
    EmptyResponseValue,

    /// Create client failure
    #[error("Failed to create client {0}: {1}")]
    CreateClient(ClientId, String),
}

impl Kind {
    /// Add a given source error as context for this error kind
    ///
    /// This is typically use with `map_err` as follows:
    ///
    /// ```ignore
    /// let x = self.something.do_stuff()
    ///     .map_err(|e| error::Kind::Config.context(e))?;
    /// ```
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
