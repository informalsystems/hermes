use thiserror::Error;

use crate::ics02_client::client_type::ClientType;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum Error {
    #[error("unknown client type: {0}")]
    UnknownClientType(String),

    #[error("cannot update client because it was not found: {0}")]
    ClientNotFound(ClientId),

    #[error("consensus state not found at: {0} at height {1}")]
    ConsensusStateNotFound(ClientId, Height),

    #[error("header verification failed")]
    HeaderVerificationFailure,

    #[error("unknown client state type: {0}")]
    UnknownClientStateType(String),

    #[error("unknown client consensus state type: {0}")]
    UnknownConsensusStateType(String),

    #[error("unknown header type: {0}")]
    UnknownHeaderType(String),

    #[error("invalid raw client state, error in decoding: {0}")]
    InvalidRawClientState(String),

    #[error("invalid raw client consensus state, error in decoding: {0}")]
    InvalidRawConsensusState(String),

    #[error("invalid raw header, could not convert because {0}")]
    InvalidRawHeader(String),

    #[error("empty raw header, could not convert")]
    EmptyRawHeader,

    #[error("invalid height result: height cannot end up zero or negative")]
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

    #[error("received header is at lower than (or equal) height to client latest height")]
    StaleHeader {
        received_height: Height,
        client_latest_height: Height,
    },
}
