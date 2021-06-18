//! This module defines the various errors that be raised in the relayer.

use crate::keyring::errors::Error as KeyringError;
use crate::sdk_error::SdkError;
use flex_error::{define_error, DisplayOnly};
use http::uri::InvalidUri;
use prost::DecodeError;
use tendermint_light_client::{
    components::io::IoError as LightClientIoError, errors::Error as LightClientError,
};
use tendermint_proto::Error as TendermintProtoError;
use tendermint_rpc::endpoint::abci_query::AbciQuery;
use tendermint_rpc::endpoint::broadcast::tx_commit::TxResult;
use tendermint_rpc::Error as TendermintError;
use tonic::{
    metadata::errors::InvalidMetadataValue, transport::Error as TransportError,
    Status as GrpcStatus,
};

use ibc::{
    ics02_client::{client_type::ClientType, error as client_error},
    ics03_connection::error as connection_error,
    ics07_tendermint::error as tendermint_error,
    ics18_relayer::error as relayer_error,
    ics23_commitment::error as commitment_error,
    ics24_host::identifier::{ChainId, ChannelId, ConnectionId},
    proofs::ProofError,
};

use crate::event::monitor;

define_error! {
    Error {
        ConfigIo
            [ DisplayOnly<std::io::Error> ]
            |_| { "config I/O error" },

        Io
            [ DisplayOnly<std::io::Error> ]
            |_| { "I/O error" },

        ConfigDecode
            [ DisplayOnly<toml::de::Error> ]
            |_| { "invalid configuration" },

        ConfigEncode
            [ DisplayOnly<toml::ser::Error> ]
            |_| { "invalid configuration" },

        Rpc
            { url: tendermint_rpc::Url }
            [ DisplayOnly<TendermintError> ]
            |e| { format!("RPC error to endpoint {}", e.url) },

        AbciQuery
            { query: AbciQuery }
            |e| { format!("ABCI query returns error: {:?}", e.query) },

        CheckTx
            {
                detail: SdkError,
                tx: TxResult
            }
            |e| { format!("CheckTX Commit returns error: {0}. RawResult: {1:?}", e.detail, e.tx) },

        DeliverTx
            {
                detail: SdkError,
                tx: TxResult
            }
            |e| { format!("DeliverTx Commit returns error: {0}. RawResult: {1:?}", e.detail, e.tx) },

        WebSocket
            { url: tendermint_rpc::Url }
            |e| { format!("Websocket error to endpoint {}", e.url) },

        EventMonitor
            [ monitor::Error ]
            |_| { "event monitor error" },

        Grpc
            |_| { "GRPC error" },

        GrpcStatus
            { status: GrpcStatus }
            |e| { format!("GRPC call return error status {0}", e.status) },

        GrpcTransport
            [ DisplayOnly<TransportError> ]
            |_| { "error in underlying transport when making GRPC call" },

        GrpcResponseParam
            { param: String }
            |e| { format!("missing parameter in GRPC response: {}", e.param) },

        Decode
            [ DisplayOnly<TendermintProtoError> ]
            |_| { "error decoding protobuf" },

        LightClient
            { address: String }
            [ DisplayOnly<LightClientError> ]
            |e| { format!("Light client error for RPC address {0}", e.address) },

        LightClientIo
            { address: String }
            [ DisplayOnly<LightClientIoError> ]
            |e| { format!("Light client error for RPC address {0}", e.address) },

        ChainNotCaughtUp
            {
                address: String,
                chain_id: ChainId,
            }
            |e| { format!("node at {} running chain {} not caught up", e.address, e.chain_id) },

        PrivateStore
            |_| { "requested proof for a path in the private store" },

        Store
            [ DisplayOnly<sled::Error> ]
            |_| { "Store error" },

        Event
            |_| { "Bad Notification" },

        EmptyUpgradedClientState
            |_| { "The upgrade plan specifies no upgraded client state" },

        EmptyResponseValue
            |_| { "Empty response value" },

        EmptyResponseProof
            |_| { "Empty response proof" },

        MalformedProof
            [ ProofError ]
            |_| { "Malformed proof" },

        InvalidHeight
            [ DisplayOnly<Box<dyn std::error::Error + Send + Sync>> ]
            |_| { "Invalid height" },

        InvalidMetadata
            [ DisplayOnly<InvalidMetadataValue> ]
            |_| { "invalid metadata" },

        BuildClientStateFailure
            |_| { "Failed to create client state" },

        CreateClient
            { client_id: String }
            |e| { format!("Failed to create client {0}", e.client_id) },

        ClientStateType
            { client_state_type: String }
            |e| { format!("unexpected client state type {0}", e.client_state_type) },

        ConnectionNotFound
            { connection_id: ConnectionId }
            |e| { format!("Connection not found: {0}", e.connection_id) },

        BadConnectionState
            |_| { "bad connection state" },

        ConnOpen
            { connection_id: ConnectionId, reason: String }
            |e| {
                format!("Failed to build conn open message {0}: {1}",
                e.connection_id, e.reason)
            },

        ConnOpenInit
            { reason: String }
            |e| { format!("Failed to build conn open init: {0}", e.reason) },

        ConnOpenTry
            { reason: String }
            |e| { format!("Failed to build conn open try: {0}", e.reason) },

        ChanOpenAck
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build channel open ack {0}: {1}",
                e.channel_id, e.reason)
            },

        ChanOpenConfirm
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build channel open confirm {0}: {1}",
                e.channel_id, e.reason)
            },

        ConsensusProof
            [ ProofError ]
            |_| { "failed to build consensus proof" },

        Packet
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build packet {0}: {1}",
                e.channel_id, e.reason)
            },

        RecvPacket
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build recv packet {0}: {1}",
                e.channel_id, e.reason)
            },

        AckPacket
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build acknowledge packet {0}: {1}",
                e.channel_id, e.reason)
            },

        TimeoutPacket
            { channel_id: ChannelId, reason: String }
            |e| {
                format!("Failed to build timeout packet {0}: {1}",
                e.channel_id, e.reason)
            },

        MessageTransaction
            { reason: String }
            |e| { format!("Message transaction failure: {0}", e.reason) },

        Query
            { query: String }
            |e| { format!("Query error occurred (failed to query for {0})", e.query) },

        KeyBase
            [ DisplayOnly<KeyringError> ]
            |_| { "Keybase error" },

        Ics02
            [ client_error::Error ]
            |_| { "ICS 02 error" },

        Ics03
            [ connection_error::Error ]
            |_| { "ICS 03 error" },

        Ics07
            [ tendermint_error::Error ]
            |_| { "ICS 07 error" },

        Ics18
            [ relayer_error::Error ]
            |_| { "ICS 18 error" },

        Ics23
            [ commitment_error::Error ]
            |_| { "ICS 23 error" },

        InvalidUri
            { uri: String }
            [ DisplayOnly<InvalidUri> ]
            |e| {
                format!("error parsing URI {}", e.uri)
            },

        ChainIdentifier
            { chain_id: String }
            |e| { format!("invalid chain identifier format: {0}", e.chain_id) },

        NonProvableData
            |_| { "requested proof for data in the privateStore" },

        ChannelSend
            |_| { "failed to send through channel" },

        ChannelReceive
            |_| { "failed to receive through channel" },

        InvalidInputHeader
            |_| { "the input header is not recognized as a header for this chain" },

        Misbehaviour
            { reason: String }
            |e| { format!("error raised while submitting the misbehaviour evidence: {0}", e.reason) },

        InvalidKeyAddress
            { address: String }
            [ DisplayOnly<Box<dyn std::error::Error + Send + Sync>> ]
            |e| { format!("invalid key address: {0}", e.address) },

        Bech32Encoding
            [ DisplayOnly<bech32::Error> ]
            |_| { "bech32 encoding failed" },

        ClientTypeMismatch
            {
                expected: ClientType,
                got: ClientType,
            }
            |e| {
                format!("client type mismatch: expected '{}', got '{}'",
                e.expected, e.got)
            },

        ProtobufDecode
            { payload_type: String }
            [ DisplayOnly<DecodeError> ]
            |e| { format!("Error decoding protocol buffer for {}", e.payload_type) },

        Cbor
            [ DisplayOnly<serde_cbor::Error> ]
            | _ | { "error decoding CBOR payload" }
    }
}

// /// Various kinds of errors that can be raiser by the relayer.
// #[derive(Clone, Debug, Display)]
// pub enum Kind {
//     /// config I/O error
//     ConfigIo,

//     /// I/O error
//     Io,

//     /// invalid configuration
//     Config,

//     /// RPC error to endpoint {0}
//     Rpc(tendermint_rpc::Url),

//     /// Websocket error to endpoint {0}
//     Websocket(tendermint_rpc::Url),

//     /// event monitor error: {0}
//     EventMonitor(crate::event::monitor::ErrorDetail),

//     /// GRPC error
//     Grpc,

//     /// Light client error for RPC address {0}
//     LightClient(String),

//     /// Store error
//     Store,

//     /// Bad Notification
//     Event,

//     /// The upgrade plan specifies no upgraded client state
//     EmptyUpgradedClientState,

//     /// Empty response value
//     EmptyResponseValue,

//     /// Empty response proof
//     EmptyResponseProof,

//     /// Malformed proof
//     MalformedProof,

//     /// Invalid height
//     InvalidHeight,

//     /// Failed to create client state
//     BuildClientStateFailure,

//     /// Failed to create client {0}
//     CreateClient(String),

//     /// Connection not found: {0}
//     ConnectionNotFound(ConnectionId),

//     /// Failed to build conn open message {0}: {1}
//     ConnOpen(ConnectionId, String),

//     /// Failed to build conn open init {0}
//     ConnOpenInit(String),

//     /// Failed to build conn open try {0}
//     ConnOpenTry(String),

//     /// Failed to build conn open ack {0}: {1}
//     ConnOpenAck(ConnectionId, String),

//     /// Failed to build conn open confirm {0}: {1}
//     ConnOpenConfirm(ConnectionId, String),

//     /// Failed to build chan open msg {0}: {1}
//     ChanOpen(ChannelId, String),

//     /// Failed to build channel open init {0}
//     ChanOpenInit(String),

//     /// Failed to build channel open try {0}
//     ChanOpenTry(String),

//     /// Failed to build channel open ack {0}: {1}
//     ChanOpenAck(ChannelId, String),

//     /// Failed to build channel open confirm {0}: {1}
//     ChanOpenConfirm(ChannelId, String),

//     /// Failed to build packet {0}: {1}
//     Packet(ChannelId, String),

//     /// Failed to build recv packet {0}: {1}
//     RecvPacket(ChannelId, String),

//     /// Failed to build acknowledge packet {0}: {1}
//     AckPacket(ChannelId, String),

//     /// Failed to build timeout packet {0}: {1}
//     TimeoutPacket(ChannelId, String),

//     /// Message transaction failure: {0}
//     MessageTransaction(String),

//     /// Query error occurred (failed to query for {0})
//     Query(String),

//     /// Keybase error
//     KeyBase,

//     /// ICS 007 error
//     Ics007,

//     /// ICS 023 error
//     Ics023(ibc::ics23_commitment::error::ErrorDetail),

//     /// invalid chain identifier format: {0}
//     ChainIdentifier(String),

//     /// requested proof for data in the privateStore
//     NonProvableData,

//     /// failed to send or receive through channel
//     Channel,

//     /// the input header is not recognized as a header for this chain
//     InvalidInputHeader,

//     /// error raised while submitting the misbehaviour evidence: {0}
//     Misbehaviour(String),

//     /// invalid key address: {0}")]
//     InvalidKeyAddress(String),

//     /// bech32 encoding failed
//     Bech32Encoding(bech32::Error),

//     /// client type mismatch: expected '{expected}', got '{got}'
//     ClientTypeMismatch {
//         expected: ClientType,
//         got: ClientType,
//     },
// }

// impl Kind {
//     /// Add a given source error as context for this error kind
//     ///
//     /// This is typically use with `map_err` as follows:
//     ///
//     /// ```ignore
//     /// let x = self.something.do_stuff()
//     ///     .map_err(|e| error::Kind::Config.context(e))?;
//     /// ```
//     pub fn context(
//         self,
//         source: impl Into<Box<dyn std::error::Error + Send + Sync>>,
//     ) -> Context<Self> {
//         Context::new(self, Some(source.into()))
//     }

//     pub fn channel(err: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> Context<Self> {
//         Self::Channel.context(err)
//     }
// }
