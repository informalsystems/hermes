use super::packet::Sequence;
use crate::core::ics02_client::error as client_error;
use crate::core::ics03_connection::error as connection_error;
use crate::core::ics24_host::error::ValidationError;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};

use crate::proofs::ProofError;
use crate::signer::SignerError;
use crate::Height;

use flex_error::{define_error, TraceError};
use itertools::Itertools;
use tendermint_proto::Error as TendermintError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Ics03Connection
            [ connection_error::Error ]
            | _ | { "ics03 connection error" },

        UnknownState
            { state: i32 }
            | e | { format_args!("channel state unknown: {}", e.state) },

        UnknownFlushStatus
            { state: i32 }
            | e | { format_args!("flush status unknown: {}", e.state) },

        UnknownFlushStatusType
            { type_id: String }
            | e | { format_args!("flush status unknown: {}", e.type_id) },

        Identifier
            [ ValidationError ]
            | _ | { "identifier error" },

        UnknownOrderType
            { type_id: String }
            | e | { format_args!("channel order type unknown: {}", e.type_id) },

        InvalidConnectionHopsLength
            { expected: usize, actual: usize }
            | e | {
                format_args!(
                    "invalid connection hops length: expected {0}; actual {1}",
                    e.expected, e.actual)
            },

        InvalidPacketCounterparty
            { port_id: PortId, channel_id: ChannelId }
            | e | {
                format_args!(
                    "packet destination port {} and channel {} doesn't match the counterparty's port/channel",
                    e.port_id, e.channel_id)
            },

        InvalidVersion
            [ TraceError<TendermintError> ]
            | _ | { "invalid version" },

        InvalidFlushStatus
            { flush_status: i32 }
            | e | { format_args!("invalid flush_status value: {}", e.flush_status) },


        Signer
            [ SignerError ]
            | _ | { "invalid signer address" },

        InvalidProof
            [ ProofError ]
            | _ | { "invalid proof" },

        MissingHeight
            | _ | { "invalid proof: missing height" },

        MissingNextRecvSeq
            { port_id: PortId, channel_id: ChannelId }
        | e | {
                format_args!("Missing sequence number for receiving packets on port {0} and channel {1}",
                             e.port_id,
                             e.channel_id)
            },

        ZeroPacketSequence
            | _ | { "packet sequence cannot be 0" },

        ZeroPacketData
            | _ | { "packet data bytes cannot be empty" },

        InvalidTimeoutHeight
            | _ | { "invalid timeout height for the packet" },

        InvalidTimeoutTimestamp
            [ crate::timestamp::ParseTimestampError ]
            | _ | { "invalid timeout timestamp" },

        InvalidPacket
            | _ | { "invalid packet" },

        MissingPacket
            | _ | { "there is no packet in this message" },

        MissingChannelId
            | _ | { "missing channel id" },

        MissingCounterparty
            | _ | { "missing counterparty" },

        NoCommonVersion
            | _ | { "no common version" },

        MissingChannel
            | _ | { "missing channel end" },

        MissingUpgradeTimeout
            | _ | { "missing upgrade timeout, either a height or a timestamp must be set" },

        MissingUpgrade
            | _ | { "missing upgrade" },

        MissingUpgradeFields
            | _ | { "missing upgrade fields" },

        MissingUpgradeErrorReceipt
            | _ | { "missing upgrade error receipt" },

        MissingProposedUpgradeChannel
            | _ | { "missing proposed upgrade channel" },

        MissingProofHeight
            | _ | { "missing proof height" },

        InvalidProofHeight
            | _ | { "invalid proof height" },

        InvalidVersionLengthConnection
            | _ | { "single version must be negotiated on connection before opening channel" },

        ChannelFeatureNotSuportedByConnection
            | _ | { "the channel ordering is not supported by connection" },

        ChannelNotFound
            { port_id: PortId, channel_id: ChannelId }
            | e | {
                format_args!(
                    "the channel end ({0}, {1}) does not exist",
                    e.port_id, e.channel_id)
            },

        ChannelMismatch
            { channel_id: ChannelId }
            | e | {
                format_args!(
                    "a different channel exists (was initialized) already for the same channel identifier {0}",
                    e.channel_id)
            },

        ConnectionNotOpen
            { connection_id: ConnectionId }
            | e | {
                format_args!(
                    "the associated connection {0} is not OPEN",
                    e.connection_id)
            },

        UndefinedConnectionCounterparty
            { connection_id: ConnectionId }
            | e | {
                format_args!(
                    "Undefined counterparty connection for {0}",
                    e.connection_id)
            },

        PacketVerificationFailed
            { sequence: Sequence }
            [ client_error::Error ]
            | e | {
                format_args!(
                    "Verification fails for the packet with the sequence number {0}",
                    e.sequence)
            },

        VerifyChannelFailed
            [ client_error::Error ]
            | _ | {
                "Error verifying channel state"
            },

        InvalidAcknowledgement
            | _ | { "Acknowledgment cannot be empty" },

        AcknowledgementExists
            { sequence: Sequence }
            | e | {
                format_args!(
                    "Packet acknowledgement exists for the packet with the sequence {0}",
                    e.sequence)
            },

        MissingNextSendSeq
            { port_id: PortId, channel_id: ChannelId }
            | e | {
                format_args!("Missing sequence number for sending packets on port {0} and channel {1}",
                             e.port_id,
                             e.channel_id)
            },

        InvalidStringAsSequence
            { value: String }
            [ TraceError<core::num::ParseIntError> ]
            | e | {
                format_args!(
                    "String {0} cannot be converted to packet sequence",
                    e.value)
            },

        InvalidPacketSequence
            {
                given_sequence: Sequence,
                next_sequence: Sequence
            }
            | e | {
                format_args!(
                    "Invalid packet sequence {0} ≠ next send sequence {1}",
                    e.given_sequence, e.next_sequence)
            },

        InvalidPacketData
            {
                data: String,
            }
            | e | {
                format_args!("Invalid packet data, not a valid hex-encoded string: {}", e.data)
            },

        InvalidPacketAck
            {
                ack: String,
            }
            | e | {
                format_args!("Invalid packet ack, not a valid hex-encoded string: {}", e.ack)
            },

        LowPacketTimestamp
            | _ | { "Receiving chain block timestamp >= packet timeout timestamp" },

        InvalidPacketTimestamp
            [ crate::timestamp::ParseTimestampError ]
            | _ | { "Invalid packet timeout timestamp value" },

        ErrorInvalidConsensusState
            | _ | { "Invalid timestamp in consensus state; timestamp must be a positive value" },

        FrozenClient
            { client_id: ClientId }
            | e | {
                format_args!(
                    "Client with id {0} is frozen",
                    e.client_id)
            },

        InvalidCounterpartyChannelId
            [ ValidationError ]
            | _ | { "Invalid channel id in counterparty" },

        ChannelClosed
            { channel_id: ChannelId }
            | e | {
                format_args!(
                    "Channel {0} is Closed",
                    e.channel_id)
            },

        ChanOpenAckProofVerification
            | _ | { "Handshake proof verification fails at ChannelOpenAck" },

        PacketCommitmentNotFound
            { sequence: Sequence }
            | e | {
                format_args!(
                    "Commitment for the packet {0} not found",
                    e.sequence)
            },

        IncorrectPacketCommitment
            { sequence: Sequence }
            | e | {
                format_args!(
                    "The stored commitment of the packet {0} is incorrect",
                    e.sequence)
            },

        PacketReceiptNotFound
            { sequence: Sequence }
            | e | {
                format_args!(
                    "Receipt for the packet {0} not found",
                    e.sequence)
            },

        PacketAcknowledgementNotFound
            { sequence: Sequence }
            | e | {
                format_args!(
                    "Acknowledgment for the packet {0} not found",
                    e.sequence)
            },

        MissingNextAckSeq
            { port_id: PortId, channel_id: ChannelId }
            | e | {
                format_args!("Missing sequence number for ack packets on port {0} and channel {1}",
                             e.port_id,
                             e.channel_id)
            },

        ProcessedTimeNotFound
            {
                client_id: ClientId,
                height: Height,
            }
            | e | {
                format_args!(
                    "Processed time for the client {0} at height {1} not found",
                    e.client_id, e.height)
            },

        ProcessedHeightNotFound
            {
                client_id: ClientId,
                height: Height,
            }
            | e | {
                format_args!(
                    "Processed height for the client {0} at height {1} not found",
                    e.client_id, e.height)
            },

        RouteNotFound
            | _ | { "route not found" },

        ImplementationSpecific
            | _ | { "implementation specific error" },

        AppModule
            { description: String }
            | e | {
                format_args!(
                    "application module error: {0}",
                    e.description)
            },

        AbciConversionFailed
            { abci_event: String }
            | e | { format_args!("Failed to convert abci event to IbcEvent: {}", e.abci_event)},

        ParseConnectionHopsVector
            { failures: Vec<(String, ValidationError)> }
            | e | {
                let failures = e.failures
                    .iter()
                    .map(|(s, e)| format!("\"{}\": {}", s, e))
                    .join(", ");

                format!("error parsing a vector of ConnectionId: {}", failures)
            },

        MalformedEventAttributeKey
            | _ | { format_args!("event attribute key is not valid UTF-8") },

        MalformedEventAttributeValue
            { key: String }
            | e | { format_args!("event attribute value for key {} is not valid UTF-8", e.key) },
    }
}

impl Error {
    pub fn chan_open_confirm_proof_verification(e: Error) -> Error {
        e.add_trace(&"Handshake proof verification fails at ChannelOpenConfirm")
    }
}
