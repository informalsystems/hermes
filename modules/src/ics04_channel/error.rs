pub type Error = anyhow::Error;

use flex_error::*;

use super::packet::Sequence;
use crate::ics04_channel::channel::State;
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::{ics02_client, Height};

define_error! {
    #[derive(Debug)]
    ChannelError {
        UnknownState
        [DisplayError<Error>]
        | _ | { format_args!("channel state unknown")},

        Identifier
        [DisplayError<Error>]
        | _ | { format_args!("identifier error")},

        UnknownOrderType
        [DisplayError<Error>]
        | _ | { format_args!("channel order type unknown")},

        InvalidConnectionHopsLength
        {left: usize, right: usize}
        | e | { format_args!("invalid connection hops length: expected {0}; actual {1}", e.left, e.right)},

        InvalidPacketCounterparty
        {port_id: PortId, channel_id: ChannelId}
        | _ | { format_args!("packet destination port/channel doesn't match the counterparty's port/channel")},

        InvalidVersion
        [DisplayError<Error>]
        | _ | { format_args!("invalid version")},

        InvalidSigner
        | _ | { format_args!("invalid signer address")},

        InvalidProof
        [DisplayError<Error>]
        | _ | { format_args!("invalid proof")},

        MissingHeight
        [DisplayError<Error>]
        | _ | { format_args!("invalid proof: missing height")},

        MissingNextRecvSeq
        | _ | { format_args!("Missing sequence number for receiving packets")},

        ZeroPacketSequence
        | _ | { format_args!("packet sequence cannot be 0")},

        ZeroPacketData
        | _ | { format_args!("packet data bytes cannot be empty")},

        ZeroPacketTimeout
        | _ | { format_args!("packet timeout height and packet timeout timestamp cannot both be 0")},

        InvalidTimeoutHeight
        [DisplayError<Error>]
        | _ | { format_args!("invalid timeout height for the packet")},

        InvalidPacket
        [DisplayError<Error>]
        | _ | { format_args!("invalid packet")},

        MissingPacket
        [DisplayError<Error>]
        | _ | { format_args!("there is no packet in this message")},

        PacketAlreadyReceived
        {sequence: Sequence}
        | e | { format_args!("Packet with the sequence number {0} has been already received", e.sequence)},

        MissingCounterparty
        | _ | { format_args!("missing counterparty")},

        NoCommonVersion
        | _ | { format_args!("no commong version")},

        MissingChannel
        | _ | { format_args!("missing channel end")},

        MissingConnection
        [DisplayError<Error>]
        | _ | { format_args!("given connection hop does not exist")},

        NoPortCapability
        {port_id: PortId}
        | e | { format_args!("the port {0} has no capability associated", e.port_id)},

        InvalidPortCapability
        | _ | { format_args!("the module associated with the port does not have the capability it needs")},

        InvalidVersionLengthConnection
        | _ | { format_args!("single version must be negociated on connection before opening channel")},

        ChannelFeatureNotSuportedByConnection
        | _ | { format_args!("the channel ordering is not supported by connection ")},

        ChannelNotFound
        {port_id: PortId, channel_id: ChannelId}
        [DisplayError<Error>]
        | e | { format_args!("the channel end ({0}, {1}) does not exist", e.port_id, e.channel_id)},

        ChannelMismatch
        {channel_id: ChannelId}
        [DisplayError<Error>]
        | e | { format_args!("a different channel exists (was initialized) already for the same channel identifier {0}", e.channel_id)},

        ConnectionNotOpen
        {connection_id: ConnectionId}
        | e | { format_args!("the associated connection {0} is not OPEN ", e.connection_id)},

        UndefinedConnectionCounterparty
        {connection_id: ConnectionId}
        | e | { format_args!("Undefined counterparty connection for {0}", e.connection_id)},

        FailedChanneOpenTryVerification
        [DisplayError<Error>]
        | _ | { format_args!("Channel chain verification fails on ChannelOpenTry for ChannelOpenInit")},

        PacketVerificationFailed
        {sequence: Sequence}
        | e | { format_args!("Verification fails for the packet with the sequence number {0}", e.sequence)},

        InvalidAcknowledgement
        | _ | { format_args!("Acknowledgment cannot be empty")},

        AcknowledgementExists
        {sequence: Sequence}
        | e | { format_args!("Packet acknowledgement exists for the packet with the sequence {0}", e.sequence)},

        MissingClientState
        {client_id: ClientId}
        | e | { format_args!("No client state associated with client id {0}", e.client_id)},

        MissingNextSendSeq
        | _ | { format_args!("Missing sequence number for send packets")},

        InvalidPacketSequence
        {sequence_left: Sequence, sequence_right: Sequence }
        | e | { format_args!("Invalid packet sequence {0} ≠ next send sequence {1}", e.sequence_left, e.sequence_right)},

        LowPacketHeight
        {height_left: Height, height_right: Height}
        | e | { format_args!("Receiving chain block height {0} >= packet timeout height {1}", e.height_left, e.height_right)},

        PacketTimeoutHeightNotReached
        {height_left: Height, height_right: Height}
        | e | { format_args!("Packet timeout height {0} > chain height {1}", e.height_left, e.height_right)},

        PacketTimeoutTimestampNotReached
        {time_left: u64, time_right: u64}
        | e | { format_args!("Packet timeout timestamp {0} > chain timestamp {1}", e.time_left, e.time_right)},

        LowPacketTimestamp
        | _ | { format_args!("Receiving chain block timestamp >= packet timeout timestamp")},

        ErrorInvalidConsensusState
        { kind: ics02_client::error::ClientError }
        | _ | { format_args!("Invalid timestamp in consensus state; timestamp must be a positive value")},

        FrozenClient
        {client_id: ClientId}
        | e | { format_args!("Client with id {0} is frozen", e.client_id)},

        MissingClientConsensusState
        {client_id: ClientId, height: Height}
        | e | { format_args!("Missing client consensus state for client id {0} at height {1}", e.client_id, e.height)},

        InvalidCounterpartyChannelId
        | _ | { format_args!("Invalid channel id in counterparty")},

        ClientNotFound
        | _ | { format_args!("Client not found in chan open verification")},

        InvalidChannelState
        {channel_id: ChannelId, state: State}
        | e | { format_args!("Channel {0} should not be state {1}", e.channel_id, e.state)},

        ChannelClosed
        {channel_id: ChannelId}
        | e | { format_args!("Channel {0} is Closed", e.channel_id)},

        ChanOpenAckProofVerification
        [DisplayError<Error>]
        | _ | { format_args!("Handshake proof verification fails at ChannelOpenAck")},

        PacketCommitmentNotFound
        {sequence: Sequence}
        | e | { format_args!("Commitment for the packet {0} not found", e.sequence)},

        ChanOpenConfirmProofVerification
        [DisplayError<Error>]
        | _ | { format_args!("Handshake proof verification fails at ChannelOpenConfirm")},

        IncorrectPacketCommitment
        {sequence: Sequence}
        | e | { format_args!("The stored commitment of the packet {0} is incorrect", e.sequence)},

        MissingNextAckSeq
        | _ | { format_args!("Missing sequence number for ack packets")},

        InFallible
        [ DisplayError<Error> ]
        |_| { format_args!("infallible") },

        Attribute
        [ DisplayError<Error> ]
        |e| { format_args!("{}", e.source) },

        ValidationKind
        [DisplayError<Error>]
        | e | { format_args!("{}", e.source) },

        SomeAttribute
        [ DisplayError<Error>]
        |e| { format_args!("{}", e.source)},

        Unknown
        | _ | { format_args!("unknown error") },

        ParseInt
        [ DisplayError<Error>]
        |_| { format_args!("parse int error") },

    }
}
