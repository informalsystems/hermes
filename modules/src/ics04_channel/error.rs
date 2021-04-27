use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

use super::packet::Sequence;
use crate::ics04_channel::channel::State;
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::timestamp::Timestamp;
use crate::{ics02_client, Height};

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum Kind {
    #[error("channel state unknown")]
    UnknownState,

    #[error("identifier error")]
    IdentifierError,

    #[error("channel order type unknown")]
    UnknownOrderType,

    #[error("invalid connection hops length: expected {0}; actual {1}")]
    InvalidConnectionHopsLength(usize, usize),

    #[error("packet destination port/channel doesn't match the counterparty's port/channel")]
    InvalidPacketCounterparty(PortId, ChannelId),

    #[error("invalid version")]
    InvalidVersion,

    #[error("invalid signer address")]
    InvalidSigner,

    #[error("invalid proof")]
    InvalidProof,

    #[error("invalid proof: missing height")]
    MissingHeight,

    #[error("Missing sequence number for receiving packets")]
    MissingNextRecvSeq,

    #[error("packet sequence cannot be 0")]
    ZeroPacketSequence,

    #[error("packet data bytes cannot be empty")]
    ZeroPacketData,

    #[error("packet timeout height and packet timeout timestamp cannot both be 0")]
    ZeroPacketTimeout,

    #[error("invalid timeout height for the packet")]
    InvalidTimeoutHeight,

    #[error("invalid packet")]
    InvalidPacket,

    #[error("there is no packet in this message")]
    MissingPacket,

    #[error("Packet with the sequence number {0} has been already received")]
    PacketAlreadyReceived(Sequence),

    #[error("missing counterparty")]
    MissingCounterparty,
    #[error("no commong version")]
    NoCommonVersion,

    #[error("missing channel end")]
    MissingChannel,

    #[error("given connection hop {0} does not exist")]
    MissingConnection(ConnectionId),

    #[error("the port {0} has no capability associated")]
    NoPortCapability(PortId),

    #[error("the module associated with the port does not have the capability it needs")]
    InvalidPortCapability,

    #[error("single version must be negociated on connection before opening channel")]
    InvalidVersionLengthConnection,

    #[error("the channel ordering is not supported by connection ")]
    ChannelFeatureNotSuportedByConnection,

    #[error("the channel end ({0}, {1}) does not exist")]
    ChannelNotFound(PortId, ChannelId),

    #[error(
        "a different channel exists (was initialized) already for the same channel identifier {0}"
    )]
    ChannelMismatch(ChannelId),

    #[error("the associated connection {0} is not OPEN ")]
    ConnectionNotOpen(ConnectionId),

    #[error("Undefined counterparty connection for {0}")]
    UndefinedConnectionCounterparty(ConnectionId),

    #[error("Channel chain verification fails on ChannelOpenTry for ChannelOpenInit")]
    FailedChanneOpenTryVerification,

    #[error("Verification fails for the packet with the sequence number {0}")]
    PacketVerificationFailed(Sequence),

    #[error("Acknowledgment cannot be empty")]
    InvalidAcknowledgement,

    #[error("Packet acknowledgement exists for the packet with the sequence {0}")]
    AcknowledgementExists(Sequence),

    #[error("No client state associated with client id {0}")]
    MissingClientState(ClientId),

    #[error("Missing sequence number for send packets")]
    MissingNextSendSeq,

    #[error("Invalid packet sequence {0} ≠ next send sequence {1}")]
    InvalidPacketSequence(Sequence, Sequence),

    #[error("Receiving chain block height {0} >= packet timeout height {1}")]
    LowPacketHeight(Height, Height),

    #[error("Packet timeout height {0} > chain height {1}")]
    PacketTimeoutHeightNotReached(Height, Height),

    #[error("Packet timeout timestamp {0} > chain timestamp {1}")]
    PacketTimeoutTimestampNotReached(Timestamp, Timestamp),

    #[error("Receiving chain block timestamp >= packet timeout timestamp")]
    LowPacketTimestamp,

    #[error("Invalid packet timeout timestamp value")]
    InvalidPacketTimestamp,

    #[error("Invalid timestamp in consensus state; timestamp must be a positive value")]
    ErrorInvalidConsensusState(ics02_client::error::Kind),

    #[error("Client with id {0} is frozen")]
    FrozenClient(ClientId),

    #[error("Missing client consensus state for client id {0} at height {1}")]
    MissingClientConsensusState(ClientId, Height),

    #[error("Invalid channel id in counterparty")]
    InvalidCounterpartyChannelId,

    #[error("Client not found in chan open verification")]
    ClientNotFound,

    #[error("Channel {0} should not be state {1}")]
    InvalidChannelState(ChannelId, State),

    #[error("Channel {0} is Closed")]
    ChannelClosed(ChannelId),

    #[error("Handshake proof verification fails at ChannelOpenAck")]
    ChanOpenAckProofVerification,

    #[error("Commitment for the packet {0} not found")]
    PacketCommitmentNotFound(Sequence),

    #[error("Handshake proof verification fails at ChannelOpenConfirm")]
    ChanOpenConfirmProofVerification,

    #[error("The stored commitment of the packet {0} is incorrect")]
    IncorrectPacketCommitment(Sequence),

    #[error("Missing sequence number for ack packets")]
    MissingNextAckSeq,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
