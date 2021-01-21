use anomaly::{BoxError, Context};
use thiserror::Error;

use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

pub type Error = anomaly::Error<Kind>;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Kind {
    #[error("unknown client type: {0}")]
    UnknownClientType(String),

    #[error("Client identifier constructor failed for type {0} with counter {1}")]
    ClientIdentifierConstructor(ClientType, u64),

    #[error("client already exists: {0}")]
    ClientAlreadyExists(ClientId),

    #[error("client not found: {0}")]
    ClientNotFound(ClientId),

    #[error("consensus state not found at: {0} at height {1}")]
    ConsensusStateNotFound(ClientId, Height),

    #[error("implementation specific")]
    ImplementationSpecific,

    #[error("header verification failed")]
    HeaderVerificationFailure,

    #[error("unknown client state type: {0}")]
    UnknownClientStateType(String),

    #[error("empty client state")]
    EmptyClientState,

    #[error("unknown client consensus state type: {0}")]
    UnknownConsensusStateType(String),

    #[error("empty client consensus state")]
    EmptyConsensusState,

    #[error("unknown header type: {0}")]
    UnknownHeaderType(String),

    #[error("invalid raw client state")]
    InvalidRawClientState,

    #[error("invalid raw client consensus state")]
    InvalidRawConsensusState,

    #[error("invalid identifer")]
    InvalidIdentifier,

    #[error("invalid raw header")]
    InvalidRawHeader,

    #[error("invalid height result")]
    InvalidHeightResult,

    #[error("invalid address")]
    InvalidAddress,

    #[error("mismatch between client and arguments types, expected: {0:?}")]
    ClientArgsTypeMismatch(ClientType),

    #[error("mismatch raw client consensus state")]
    RawClientAndConsensusStateTypesMismatch {
        state_type: ClientType,
        consensus_type: ClientType,
    },
}

impl Kind {
    pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
