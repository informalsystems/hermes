use anomaly::{BoxError, Context};
use thiserror::Error;

pub type Error = anomaly::Error<Kind>;

use crate::ics24_host::identifier::{ChannelId, ConnectionId};

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("channel state unknown")]
    UnknownState,

    #[error("identifier error")]
    IdentifierError,

    #[error("channel order type unknown")]
    UnknownOrderType,

    #[error("invalid connection hops length")]
    InvalidConnectionHopsLength,

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

    #[error("the port has no capability associated")]
    NoPortCapability,

    #[error("the module associated with the port does not have the capability it needs")]
    InvalidPortCapability,

    #[error("single version must be negociated on connection before opening channel")]
    InvalidVersionLengthConnection,

    #[error("the channel ordering is not supported by connection ")]
    ChannelFeatureNotSuportedByConnection,

    #[error("queried for a non-existing connection")]
    ChannelNotFound,

    #[error(
        "a different channel exists (was initialized) already for the same channel identifier {0}"
    )]
    ChannelMismatch(ChannelId),

    #[error("the associated connection {0} is not OPEN ")]
    ConnectionNotOpen(ConnectionId),

    #[error("Undefined counterparty connection for {0}")]
    UndefinedConnectionCounterparty(ConnectionId),

    #[error("Channel chain verification fails")]
    FailedChanneOpenTryVerification,

    #[error("No client state associated with the channel")]
    MissingClientState,

    #[error("Frozen Client")]
    FrozenClient,

    #[error("Missing client consensus state")]
    MissingClientConsensusState,

    #[error("Invalid channel id in counterparty")]
    InvalidCounterpartyChannelId,

    #[error("Client not found in chan open verification")]
    ClientNotFound,
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
