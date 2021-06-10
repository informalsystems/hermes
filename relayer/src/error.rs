//! This module defines the various errors that be raised in the relayer.

use anomaly::{BoxError, Context};
use thiserror::Error;

use ibc::{
    ics02_client::{client_type::ClientType, error::Kind as Ics02Error},
    ics24_host::identifier::{ChainId, ChannelId, ConnectionId},
};

use tendermint_light_client::errors::ErrorKind as LightClientError;
use tendermint_rpc::Url;

use crate::util::retry::RetryableError;

/// An error that can be raised by the relayer.
pub type Error = anomaly::Error<Kind>;

/// Various kinds of errors that can be raiser by the relayer.
#[derive(Clone, Debug, Error)]
pub enum Kind {
    /// Config I/O error
    #[error("config I/O error")]
    ConfigIo,

    /// I/O error
    #[error("I/O error")]
    Io,

    /// Invalid configuration
    #[error("invalid configuration")]
    Config,

    /// RPC error (typically raised by the RPC client or the RPC requester)
    #[error("RPC error to endpoint {0}")]
    Rpc(Url),

    /// Websocket error (typically raised by the Websocket client)
    #[error("Websocket error to endpoint {0}")]
    Websocket(Url),

    /// Event monitor error
    #[error("event monitor error: {0}")]
    EventMonitor(crate::event::monitor::Error),

    /// GRPC error (typically raised by the GRPC client or the GRPC requester)
    #[error("GRPC error")]
    Grpc,

    /// Light client instance error, typically raised by a `Client`
    #[error("Light client error for RPC address {0}")]
    LightClient(String, LightClientError),

    #[error("Light client error for RPC address")]
    LightClientNotUpToDate(Url, ChainId),

    /// Trusted store error, raised by instances of `Store`
    #[error("Store error")]
    Store,

    /// Event error (raised by the event monitor)
    #[error("Bad Notification")]
    Event,

    /// Missing ClientState in the upgrade CurrentPlan
    #[error("The upgrade plan specifies no upgraded client state")]
    EmptyUpgradedClientState,

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
    #[error("Failed to create client {0}")]
    CreateClient(String),

    #[error("Connection not found: {0}")]
    ConnectionNotFound(ConnectionId),

    /// Common failures to all connection messages
    #[error("Failed to build conn open message {0}: {1}")]
    ConnOpen(ConnectionId, String),

    /// Connection open init failure
    #[error("Failed to build conn open init {0}")]
    ConnOpenInit(String),

    /// Connection open try failure
    #[error("Failed to build conn open try {0}")]
    ConnOpenTry(String),

    /// Connection open ack failure
    #[error("Failed to build conn open ack {0}: {1}")]
    ConnOpenAck(ConnectionId, String),

    /// Connection open confirm failure
    #[error("Failed to build conn open confirm {0}: {1}")]
    ConnOpenConfirm(ConnectionId, String),

    /// Common failures to all channel messages
    #[error("Failed to build chan open msg {0}: {1}")]
    ChanOpen(ChannelId, String),

    /// Channel open init failure
    #[error("Failed to build channel open init {0}")]
    ChanOpenInit(String),

    /// Channel open try failure
    #[error("Failed to build channel open try {0}")]
    ChanOpenTry(String),

    /// Channel open ack failure
    #[error("Failed to build channel open ack {0}: {1}")]
    ChanOpenAck(ChannelId, String),

    /// Channel open confirm failure
    #[error("Failed to build channel open confirm {0}: {1}")]
    ChanOpenConfirm(ChannelId, String),

    /// Packet build failure
    #[error("Failed to build packet {0}: {1}")]
    Packet(ChannelId, String),

    /// Packet recv  failure
    #[error("Failed to build recv packet {0}: {1}")]
    RecvPacket(ChannelId, String),

    /// Packet acknowledgement failure
    #[error("Failed to build acknowledge packet {0}: {1}")]
    AckPacket(ChannelId, String),

    /// Packet timeout  failure
    #[error("Failed to build timeout packet {0}: {1}")]
    TimeoutPacket(ChannelId, String),

    /// A message transaction failure
    #[error("Message transaction failure: {0}")]
    MessageTransaction(String),

    /// Failed query
    #[error("Query error occurred (failed to query for {0})")]
    Query(String),

    /// Keybase related error
    #[error("Keybase error")]
    KeyBase,

    #[error("ICS 02 error: {0}")]
    Ics002(Ics02Error),

    /// ICS 007 error
    #[error("ICS 007 error")]
    Ics007,

    /// ICS 023 error
    #[error("ICS 023 error")]
    Ics023(#[from] ibc::ics23_commitment::error::Error),

    /// Invalid chain identifier
    #[error("invalid chain identifier format: {0}")]
    ChainIdentifier(String),

    #[error("requested proof for data in the privateStore")]
    NonProvableData,

    #[error("failed to send or receive through channel")]
    Channel,

    #[error("the input header is not recognized as a header for this chain")]
    InvalidInputHeader,

    #[error("error raised while submitting the misbehaviour evidence: {0}")]
    Misbehaviour(String),

    #[error("invalid key address: {0}")]
    InvalidKeyAddress(String),

    #[error("bech32 encoding failed")]
    Bech32Encoding(#[from] bech32::Error),

    #[error("client type mismatch: expected '{expected}', got '{got}'")]
    ClientTypeMismatch {
        expected: ClientType,
        got: ClientType,
    },
}

impl RetryableError for Kind {
    #[allow(clippy::match_like_matches_macro)]
    fn is_retryable(&self) -> bool {
        match self {
            Kind::Io => true,
            Kind::Ics002(e) => e.is_retryable(),
            Kind::LightClient(_, e) => e.is_retryable(),

            // TODO: actually classify the remaining variants on whether they are retryable
            _ => true,
        }
    }
}

impl RetryableError for LightClientError {
    #[allow(clippy::match_like_matches_macro)]
    fn is_retryable(&self) -> bool {
        match self {
            // Only IO error in light client should be retried
            LightClientError::Io(_) => true,
            _ => false,
        }
    }
}

impl RetryableError for Ics02Error {
    #[allow(clippy::match_like_matches_macro)]
    fn is_retryable(&self) -> bool {
        // By default all client errors are non-retryable
        // TODO: actually classify the remaining variants on whether they are retryable
        false
    }
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

    pub fn channel(err: impl Into<BoxError>) -> Context<Self> {
        Self::Channel.context(err)
    }
}
