//! This module defines the various errors that be raised in the relayer.

use anomaly::Context;
use displaydoc::Display;

use ibc::{
    ics02_client::client_type::ClientType,
    ics24_host::identifier::{ChannelId, ConnectionId},
};

/// An error that can be raised by the relayer.
pub type Error = anomaly::Error<Kind>;

impl std::error::Error for Kind {}

/// Various kinds of errors that can be raiser by the relayer.
#[derive(Clone, Debug, Display)]
pub enum Kind {
    /// config I/O error
    ConfigIo,

    /// I/O error
    Io,

    /// invalid configuration
    Config,

    /// RPC error to endpoint {0}
    Rpc(tendermint_rpc::Url),

    /// Websocket error to endpoint {0}
    Websocket(tendermint_rpc::Url),

    /// event monitor error: {0}
    EventMonitor(crate::event::monitor::Error),

    /// GRPC error
    Grpc,

    /// Light client error for RPC address {0}
    LightClient(String),

    /// Store error
    Store,

    /// Bad Notification
    Event,

    /// The upgrade plan specifies no upgraded client state
    EmptyUpgradedClientState,

    /// Empty response value
    EmptyResponseValue,

    /// Empty response proof
    EmptyResponseProof,

    /// Malformed proof
    MalformedProof,

    /// Invalid height
    InvalidHeight,

    /// Failed to create client state
    BuildClientStateFailure,

    /// Failed to create client {0}
    CreateClient(String),

    /// Connection not found: {0}
    ConnectionNotFound(ConnectionId),

    /// Failed to build conn open message {0}: {1}
    ConnOpen(ConnectionId, String),

    /// Failed to build conn open init {0}
    ConnOpenInit(String),

    /// Failed to build conn open try {0}
    ConnOpenTry(String),

    /// Failed to build conn open ack {0}: {1}
    ConnOpenAck(ConnectionId, String),

    /// Failed to build conn open confirm {0}: {1}
    ConnOpenConfirm(ConnectionId, String),

    /// Failed to build chan open msg {0}: {1}
    ChanOpen(ChannelId, String),

    /// Failed to build channel open init {0}
    ChanOpenInit(String),

    /// Failed to build channel open try {0}
    ChanOpenTry(String),

    /// Failed to build channel open ack {0}: {1}
    ChanOpenAck(ChannelId, String),

    /// Failed to build channel open confirm {0}: {1}
    ChanOpenConfirm(ChannelId, String),

    /// Failed to build packet {0}: {1}
    Packet(ChannelId, String),

    /// Failed to build recv packet {0}: {1}
    RecvPacket(ChannelId, String),

    /// Failed to build acknowledge packet {0}: {1}
    AckPacket(ChannelId, String),

    /// Failed to build timeout packet {0}: {1}
    TimeoutPacket(ChannelId, String),

    /// Message transaction failure: {0}
    MessageTransaction(String),

    /// Query error occurred (failed to query for {0})
    Query(String),

    /// Keybase error
    KeyBase,

    /// ICS 007 error
    Ics007,

    /// ICS 023 error
    Ics023(ibc::ics23_commitment::error::ErrorDetail),

    /// invalid chain identifier format: {0}
    ChainIdentifier(String),

    /// requested proof for data in the privateStore
    NonProvableData,

    /// failed to send or receive through channel
    Channel,

    /// the input header is not recognized as a header for this chain
    InvalidInputHeader,

    /// error raised while submitting the misbehaviour evidence: {0}
    Misbehaviour(String),

    /// invalid key address: {0}")]
    InvalidKeyAddress(String),

    /// bech32 encoding failed
    Bech32Encoding(bech32::Error),

    /// client type mismatch: expected '{expected}', got '{got}'
    ClientTypeMismatch {
        expected: ClientType,
        got: ClientType,
    },
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
    pub fn context(
        self,
        source: impl Into<Box<dyn std::error::Error + Send + Sync>>,
    ) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }

    pub fn channel(err: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> Context<Self> {
        Self::Channel.context(err)
    }
}
