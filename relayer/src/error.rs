//! This module defines the various errors that be raised in the relayer.

use crate::sdk_error::{sdk_error_from_tx_result, SdkError};
use crate::util::retry::RetryableError;
use anomaly::{BoxError, Context};
use crossbeam_channel::{RecvError, SendError};
use http::uri::InvalidUri;
use ibc::{
    ics02_client::{client_type::ClientType, error::Error as ClientError},
    ics24_host::identifier::{ChannelId, ConnectionId},
};
use prost::DecodeError;
use std::any::type_name;
use std::fmt::Debug;
use tendermint_rpc::endpoint::abci_query::AbciQuery;
use tendermint_rpc::endpoint::broadcast::tx_commit::TxResult;
use tendermint_rpc::Error as TendermintRpcError;
use thiserror::Error;
use tonic::{transport::Error as TransportError, Status};

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
    #[error("call to Tendermint RPC endpoint {0} returned error")]
    TendermintRpc(tendermint_rpc::Url),

    #[error("ABCI query returns error: {0:?}")]
    AbciQuery(AbciQuery),

    #[error("CheckTX Commit returns error: {0}. RawResult: {1:?}")]
    CheckTx(SdkError, TxResult),

    #[error("DeliverTX Commit returns error: {0}. RawResult: {1:?}")]
    DeliverTx(SdkError, TxResult),

    /// Websocket error (typically raised by the Websocket client)
    #[error("Websocket error to endpoint {0}")]
    Websocket(tendermint_rpc::Url),

    /// Event monitor error
    #[error("event monitor error: {0}")]
    EventMonitor(crate::event::monitor::Error),

    /// GRPC error (typically raised by the GRPC client or the GRPC requester)
    #[error("GRPC error")]
    Grpc,

    #[error("GRPC call return error status {0}")]
    GrpcStatus(Status),

    #[error("error in underlying transport when making GRPC call")]
    GrpcTransport,

    #[error("missing parameter in GRPC response: {0}")]
    GrpcResponseParam(String),

    /// Light client instance error, typically raised by a `Client`
    #[error("Light client error for RPC address {0}")]
    LightClient(String),

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

    #[error("Error converting from raw client state")]
    InvalidRawClientState,

    /// Create client failure
    #[error("Failed to create client {0}")]
    CreateClient(String),

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

    #[error("Error decoding protocol buffer for {0}")]
    ProtobufDecode(String),

    /// Failed query
    #[error("Query error occurred (failed to query for {0})")]
    Query(String),

    /// Keybase related error
    #[error("Key ring error: {0}")]
    KeyRing(crate::keyring::errors::Kind),

    /// ICS 007 error
    #[error("ICS 007 error")]
    Ics007,

    /// ICS 023 error
    #[error("ICS 023 error")]
    Ics023(ibc::ics23_commitment::error::Error),

    #[error("ICS 018 error: {0}")]
    Ics18(ibc::ics18_relayer::error::Kind),

    #[error("error parsing URI {0} - {0}")]
    InvalidUri(String, String),

    /// Invalid chain identifier
    #[error("invalid chain identifier format: {0}")]
    ChainIdentifier(String),

    #[error("requested proof for data in the privateStore")]
    NonProvableData,

    #[error("failed to send or receive through channel")]
    ChannelSend,

    #[error("failed to send or receive through channel")]
    ChannelReceive,

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
    fn is_retryable(&self) -> bool {
        // TODO: actually classify whether an error kind is retryable
        true
    }
}

fn error_with_source(err: Kind, source: impl Into<BoxError>) -> Error {
    Context::new(err, Some(source.into())).into()
}

fn error(err: Kind) -> Error {
    Context::new(err, None).into()
}

pub fn send_error<T>(err: SendError<T>) -> Error
where
    T: Send + Sync + 'static,
{
    error_with_source(Kind::ChannelSend, err)
}

pub fn recv_error(err: RecvError) -> Error {
    error_with_source(Kind::ChannelReceive, err)
}

pub fn grpc_status_error(status: Status) -> Error {
    error(Kind::GrpcStatus(status))
}

pub fn grpc_transport_error(err: TransportError) -> Error {
    error_with_source(Kind::GrpcTransport, err)
}

pub fn grpc_response_param_error(msg: &str) -> Error {
    error(Kind::GrpcResponseParam(msg.to_string()))
}

pub fn tendermint_rpc_error(url: &tendermint_rpc::Url, err: TendermintRpcError) -> Error {
    error_with_source(Kind::TendermintRpc(url.clone()), err)
}

pub fn abci_query_error(query: AbciQuery) -> Error {
    error(Kind::AbciQuery(query))
}

pub fn invalid_uri_error(uri: String, err: InvalidUri) -> Error {
    error(Kind::InvalidUri(uri, format!("{}", err)))
}

pub fn protobuf_decode_error<T>(err: DecodeError) -> Error {
    error_with_source(Kind::ProtobufDecode(type_name::<T>().to_string()), err)
}

pub fn invalid_raw_client_state_error(err: ClientError) -> Error {
    error_with_source(Kind::InvalidRawClientState, err)
}

pub fn ics18_relayer_error(err: ibc::ics18_relayer::error::Error) -> Error {
    error_with_source(Kind::Ics18(err.kind().clone()), err)
}

pub fn keyring_error(err: crate::keyring::errors::Error) -> Error {
    error_with_source(Kind::KeyRing(err.kind().clone()), err)
}

pub fn check_tx_error(result: TxResult) -> Error {
    error(Kind::CheckTx(sdk_error_from_tx_result(&result), result))
}

pub fn deliver_tx_error(result: TxResult) -> Error {
    error(Kind::DeliverTx(sdk_error_from_tx_result(&result), result))
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
