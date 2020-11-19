//! This module defines the various errors that be raised in the relayer.

use anomaly::{BoxError, Context};
use ibc::ics24_host::identifier::{ChannelId, ClientId, ConnectionId};
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

    /// GRPC error (typically raised by the GRPC client or the GRPC requester)
    #[error("GRPC error")]
    Grpc,

    /// Light client error, typically raised by a `Client`
    #[error("Light client error")]
    LightClient,

    /// Trusted store error, raised by instances of `Store`
    #[error("Store error")]
    Store,

    /// Event error (raised by the event monitor)
    #[error("Bad Notification")]
    Event,

    /// Response does not contain data
    #[error("Empty response value")]
    EmptyResponseValue,

    /// Response does not contain a proof
    #[error("Empty response proof")]
    EmptyResponseProof,

    /// Response does not contain a proof
    #[error("Malformed proof")]
    MalformedProof,

    /// Invalid height
    #[error("Invalid height")]
    InvalidHeight,

    /// Unable to build the client state
    #[error("Failed to create client state")]
    BuildClientStateFailure,

    /// Create client failure
    #[error("Failed to create client {0}: {1}")]
    CreateClient(ClientId, String),

    /// Connection open init failure
    #[error("Failed to build conn open init {0}: {1}")]
    ConnOpenInit(ConnectionId, String),

    /// Connection open try failure
    #[error("Failed to build conn open try {0}: {1}")]
    ConnOpenTry(ConnectionId, String),

    /// Connection open ack failure
    #[error("Failed to build conn open ack {0}: {1}")]
    ConnOpenAck(ConnectionId, String),

    /// Connection open confirm failure
    #[error("Failed to build conn open confirm {0}: {1}")]
    ConnOpenConfirm(ConnectionId, String),

    /// Channel open init failure
    #[error("Failed to build channel open init {0}: {1}")]
    ChanOpenInit(ChannelId, String),

    /// Channel open try failure
    #[error("Failed to build channel open try {0}: {1}")]
    ChanOpenTry(ChannelId, String),

    /// Channel open ack failure
    #[error("Failed to build channel open ack {0}: {1}")]
    ChanOpenAck(ChannelId, String),

    /// Channel open confirm failure
    #[error("Failed to build channel open confirm {0}: {1}")]
    ChanOpenConfirm(ChannelId, String),

    /// A message transaction failure
    #[error("Message transaction failure: {0}")]
    MessageTransaction(String),

    /// Failed query
    #[error("Bad parameter")]
    Query,

    /// Keybase related error
    #[error("Keybase error")]
    KeyBase,
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
