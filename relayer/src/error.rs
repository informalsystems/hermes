//! This module defines the various errors that be raised in the relayer.

use core::time::Duration;

use flex_error::{define_error, DisplayOnly, TraceClone, TraceError};
use http::uri::InvalidUri;
use humantime::format_duration;
use prost::DecodeError;
use tendermint::Error as TendermintError;
use tendermint_light_client::{
    components::io::IoError as LightClientIoError, errors::Error as LightClientError,
};
use tendermint_proto::Error as TendermintProtoError;
use tendermint_rpc::endpoint::abci_query::AbciQuery;
use tendermint_rpc::endpoint::broadcast::tx_commit::TxResult;
use tendermint_rpc::Error as TendermintRpcError;
use tonic::{
    metadata::errors::InvalidMetadataValue, transport::Error as TransportError,
    Status as GrpcStatus,
};

use ibc::{
    clients::ics07_tendermint::error as tendermint_error,
    core::{
        ics02_client::{client_type::ClientType, error as client_error},
        ics03_connection::error as connection_error,
        ics23_commitment::error as commitment_error,
        ics24_host::identifier::{ChainId, ChannelId, ConnectionId},
    },
    proofs::ProofError,
    relayer::ics18_relayer::error as relayer_error,
};

use crate::chain::cosmos::GENESIS_MAX_BYTES_MAX_FRACTION;
use crate::event::monitor;
use crate::keyring::errors::Error as KeyringError;
use crate::sdk_error::SdkError;

define_error! {
    Error {
        ConfigIo
            [ TraceError<std::io::Error> ]
            |_| { "config I/O error" },

        Io
            [ TraceError<std::io::Error> ]
            |_| { "I/O error" },

        ConfigDecode
            [ TraceError<toml::de::Error> ]
            |_| { "invalid configuration" },

        ConfigEncode
            [ TraceError<toml::ser::Error> ]
            |_| { "invalid configuration" },

        Rpc
            { url: tendermint_rpc::Url }
            [ TraceClone<TendermintRpcError> ]
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
            [ TraceError<TransportError> ]
            |_| { "error in underlying transport when making GRPC call" },

        GrpcResponseParam
            { param: String }
            |e| { format!("missing parameter in GRPC response: {}", e.param) },

        Decode
            [ TraceError<TendermintProtoError> ]
            |_| { "error decoding protobuf" },

        LightClient
            { address: String }
            [ TraceError<LightClientError> ]
            |e| { format!("Light client error for RPC address {0}", e.address) },

        LightClientState
            [ client_error::Error ]
            |_| { "Light client encountered error due to client state".to_string() },

        LightClientIo
            { address: String }
            [ TraceError<LightClientIoError> ]
            |e| { format!("Light client error for RPC address {0}", e.address) },

        ChainNotCaughtUp
            {
                address: String,
                chain_id: ChainId,
            }
            |e| { format!("node at {} running chain {} not caught up", e.address, e.chain_id) },

        PrivateStore
            |_| { "Requested proof for a path in the private store" },

        Event
            |_| { "Bad notification" },

        ConversionFromAny
            [ TraceError<TendermintProtoError> ]
            |_| { "Conversion from a protobuf `Any` into a domain type failed" },

        EmptyUpgradedClientState
            |_| { "Found no upgraded client state" },

        ConsensusStateTypeMismatch
            {
                expected: ClientType,
                got: ClientType,
            }
            |e| { format!("consensus state type mismatch; hint: expected client type '{0}', got '{1}'", e.expected, e.got) },

        EmptyResponseValue
            |_| { "Empty response value" },

        EmptyResponseProof
            |_| { "Empty response proof" },

        MalformedProof
            [ ProofError ]
            |_| { "Malformed proof" },

        InvalidHeight
            [ TendermintError ]
            |_| { "Invalid height" },

        InvalidMetadata
            [ TraceError<InvalidMetadataValue> ]
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
            [ KeyringError ]
            |_| { "Keybase error" },

        Ics02
            [ client_error::Error ]
            |e| { format!("ICS 02 error: {}", e.source) },

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
            [ TraceError<InvalidUri> ]
            |e| {
                format!("error parsing URI {}", e.uri)
            },

        ChainIdentifier
            { chain_id: String }
            |e| { format!("invalid chain identifier format: {0}", e.chain_id) },

        NonProvableData
            |_| { "requested proof for data in the privateStore" },

        ChannelSend
            |_| { "internal communication failure: error sending inter-thread request/response" },

        ChannelReceive
            [ TraceError<crossbeam_channel::RecvError> ]
            |_| { "failed to receive through channel" },

        InvalidInputHeader
            |_| { "the input header is not recognized as a header for this chain" },

        TxNoConfirmation
            |_| { "Failed Tx: no confirmation" },

        Misbehaviour
            { reason: String }
            |e| { format!("error raised while submitting the misbehaviour evidence: {0}", e.reason) },

        InvalidKeyAddress
            { address: String }
            [ TendermintError ]
            |e| { format!("invalid key address: {0}", e.address) },

        Bech32Encoding
            [ TraceError<bech32::Error> ]
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
            [ TraceError<DecodeError> ]
            |e| { format!("Error decoding protocol buffer for {}", e.payload_type) },

        Cbor
            [ TraceError<serde_cbor::Error> ]
            | _ | { "error decoding CBOR payload" },

        TxSimulateGasEstimateExceeded
            {
                chain_id: ChainId,
                estimated_gas: u64,
                max_gas: u64,
            }
            |e| {
                format!("{} gas estimate {} from simulated Tx exceeds the maximum configured {}",
                    e.chain_id, e.estimated_gas, e.max_gas)
            },

        HealthCheckJsonRpc
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
            }
            [ DisplayOnly<tendermint_rpc::error::Error> ]
            |e| {
                format!("health check failed for endpoint {0} on the JSON-RPC interface of chain {1}:{2}",
                    e.endpoint, e.chain_id, e.address)
            },

        HealthCheckGrpcTransport
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
            }
            [ DisplayOnly<tonic::transport::Error> ]
            |e| {
                format!("health check failed for endpoint {0} on the gRPC interface of chain {1}:{2}",
                    e.endpoint, e.chain_id, e.address)
            },

        HealthCheckGrpcStatus
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
                status: tonic::Status
            }
            |e| {
                format!("health check failed for endpoint {0} on the gRPC interface of chain {1}:{2}; caused by: {3}",
                    e.endpoint, e.chain_id, e.address, e.status)
            },

        HealthCheckInvalidVersion
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
            }
            |e| {
                format!("health check failed for endpoint {0} on the Json RPC interface of chain {1}:{2}; the gRPC response contains no application version information",
                    e.endpoint, e.chain_id, e.address)
            },

        ConfigValidationJsonRpc
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
            }
            [ DisplayOnly<tendermint_rpc::error::Error> ]
            |e| {
                format!("semantic config validation: failed to reach endpoint {0} on the JSON-RPC interface of chain {1}:{2}",
                    e.endpoint, e.chain_id, e.address)
            },

        ConfigValidationTxSizeOutOfBounds
            {
                chain_id: ChainId,
                configured_bound: usize,
                genesis_bound: u64,
            }
            |e| {
                format!("semantic config validation failed for option `max_tx_size` chain '{}', reason: `max_tx_size` = {} is greater than {}% of the genesis block param `max_size` = {}",
                    e.chain_id, e.configured_bound, GENESIS_MAX_BYTES_MAX_FRACTION * 100.0, e.genesis_bound)
            },

        ConfigValidationTrustingPeriodSmallerThanZero
            {
                chain_id: ChainId,
                trusting_period: Duration,
            }
            |e| {
                format!("semantic config validation failed for option `trusting_period` of chain '{}', reason: trusting period ({}) must be greater than zero",
                    e.chain_id, format_duration(e.trusting_period))
            },

        ConfigValidationTrustingPeriodGreaterThanUnbondingPeriod
            {
                chain_id: ChainId,
                trusting_period: Duration,
                unbonding_period: Duration,
            }
            |e| {
                format!("semantic config validation failed for option `trusting_period` of chain '{}', reason: trusting period ({}) must be smaller than the unbonding period ({})",
                    e.chain_id, format_duration(e.trusting_period), format_duration(e.unbonding_period))
            },

        ConfigValidationDefaultGasTooHigh
            {
                chain_id: ChainId,
                default_gas: u64,
                max_gas: u64,
            }
            |e| {
                format!("semantic config validation failed for option `default_gas` of chain '{}', reason: default gas ({}) must be smaller than the max gas ({})",
                    e.chain_id, e.default_gas, e.max_gas)
            },

        SdkModuleVersion
            {
                chain_id: ChainId,
                address: String,
                cause: String
            }
            |e| {
                format!("Hermes health check failed while verifying the application compatibility for chain {0}:{1}; caused by: {2}",
                    e.chain_id, e.address, e.cause)
            },

        UnknownAccountType
            {
                type_url: String
            }
            |e| {
                format!("Failed to deserialize account of an unknown protobuf type: {0}",
                    e.type_url)
            },

        EmptyBaseAccount
            |_| { "Empty BaseAccount within EthAccount" },

    }
}

impl Error {
    pub fn send<T>(_: crossbeam_channel::SendError<T>) -> Error {
        Error::channel_send()
    }
}
