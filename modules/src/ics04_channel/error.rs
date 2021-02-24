use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

use crate::ics04_channel::channel::State;
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::Height;

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

    #[error("invalid version")]
    InvalidVersion,

    #[error("invalid signer address")]
    InvalidSigner,

    #[error("invalid proof")]
    InvalidProof,

    #[error("invalid proof: missing height")]
    MissingHeight,

    #[error("invalid timeout height for the packet")]
    InvalidTimeoutHeight,

    #[error("invalid packet")]
    InvalidPacket,

    #[error("there is no packet in this message")]
    MissingPacket,

    #[error("acknowledgement too long")]
    AcknowledgementTooLong,

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

    #[error("No client state associated with client id {0}")]
    MissingClientState(ClientId),

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

    #[error("Channel is in state {0}")]
    ChannelAlreadyClosed(ChannelId),

    #[error("Handshake proof verification fails at ChannelOpenAck")]
    ChanOpenAckProofVerification,

    #[error("Handshake proof verification fails at ChannelOpenConfirm")]
    ChanOpenConfirmProofVerification,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
