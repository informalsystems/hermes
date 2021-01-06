// TODO: Update error types for Connection!!
use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics02_client::Error as ICS2Error;
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error)]
pub enum Kind {
    #[error("connection state unknown")]
    InvalidState(i32),

    #[error("connection exists (was initialized) already: {0}")]
    ConnectionExistsAlready(ConnectionId),

    #[error("a different connection exists (was initialized) already for the same connection id {0} -> {:?}")]
    ConnectionMismatch(ConnectionId, ConnectionEnd),

    #[error("connection end for identifier {0} was never initialized")]
    UninitializedConnection(ConnectionId),

    #[error("consensus height claimed by the client on the other party is too advanced: {0} (host chain current height: {1})")]
    InvalidConsensusHeight(Height, Height),

    #[error("consensus height claimed by the client on the other party falls outside of trusting period: {0} (host chain current height: {1})")]
    StaleConsensusHeight(Height, Height),

    #[error("identifier error")]
    IdentifierError,

    #[error("invalid version")]
    InvalidVersion,

    #[error("empty supported versions")]
    EmptyVersions,

    #[error("no commong version")]
    NoCommonVersion,

    #[error("invalid address")]
    InvalidAddress,

    #[error("missing consensus proof height")]
    MissingProofHeight,

    #[error("missing consensus proof height")]
    MissingConsensusHeight,

    #[error("invalid connection proof")]
    InvalidProof,

    #[error("invalid signer")]
    InvalidSigner,

    #[error("queried for a non-existing connection id {0}")]
    ConnectionNotFound(ConnectionId),

    #[error("conversion from raw failed because the raw object is empty")]
    EmptyRawObject,

    #[error("invalid counterparty")]
    InvalidCounterparty,

    #[error("counterparty chosen connection id {0} is different than the connection id {1}")]
    ConnectionIdMismatch(ConnectionId, ConnectionId),

    #[error("missing counterparty")]
    MissingCounterparty,

    #[error("missing counterparty prefix")]
    MissingCounterpartyPrefix,

    #[error("the client id does not match any client state: {0}")]
    MissingClient(ClientId),

    #[error("client proof must be present")]
    NullClientProof,

    #[error("the client with id {0} is frozen")]
    FrozenClient(ClientId),

    #[error("the connection proof verification failed")]
    ConnectionVerificationFailure,

    #[error(
        "the expected consensus state (height {0}) for client (id {1}) could not be retrieved"
    )]
    MissingClientConsensusState(Height, ClientId),

    #[error("the local consensus state (at height {0}) could not be retrieved")]
    MissingLocalConsensusState(Height),

    #[error("the consensus proof verification failed (height: {0}) with error: {1}")]
    ConsensusStateVerificationFailure(Height, ICS2Error),

    #[error("the client state proof verification failed with error: {0}")]
    ClientStateVerificationFailure(ICS2Error),
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
