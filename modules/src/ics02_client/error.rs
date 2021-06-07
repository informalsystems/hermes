use std::num::ParseIntError;

// use anomaly::{BoxError, Context};
// use thiserror::Error;

use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::error::Error as Ics23Error;
use crate::ics24_host::error::ValidationError;
use crate::ics24_host::identifier::ClientId;
use tendermint_proto::Error as TendermintError;
use std::num::TryFromIntError;
use crate::Height;

use flex_error::{define_error, DisplayError, DetailOnly};

define_error!{ Error;

    UnknownClientType
    { client_type: String }
    | e | { format_args!("unknown client type: {0}", e.client_type) },

    ClientIdentifierConstructor
    { client_type: ClientType, counter: u64 }
    [ DisplayError<ValidationError> ]
    | e | {
        format_args!("Client identifier constructor failed for type {0} with counter {1}",
            e.client_type, e.counter)
    },

    ClientAlreadyExists
    { client_id: ClientId }
    | e | { format_args!("client already exists: {0}", e.client_id) },

    ClientNotFound
    { client_id: ClientId }
    | e | { format_args!("client not found: {0}", e.client_id) },

    ClientFrozen
    { client_id: ClientId }
    | e | { format_args!("client is frozen: {0}", e.client_id) },

    ConsensusStateNotFound
    { client_id: ClientId, height: Height }
    | e | {
        format_args!("consensus state not found at: {0} at height {1}",
            e.client_id, e.height)
    },

    ImplementationSpecific
    | _ | { format_args!("implementation specific error") },

    HeaderVerificationFailure
    { reason: String }
    | e | { format_args!("header verification failed with reason: {}", e.reason) },

    UnknownClientStateType
    { client_state_type: String }
    | e | { format_args!("unknown client state type: {0}", e.client_state_type) },

    EmptyClientStateResponse
    | _ | { format_args!("the client state was not found") },

    UnknownConsensusStateType
    { consensus_state_type: String }
    | e | {
        format_args!("unknown client consensus state type: {0}",
            e.consensus_state_type)
    },

    EmptyConsensusStateResponse
    | _ | { format_args!("the client state was not found") },

    UnknownHeaderType
    { header_type: String }
    | e | {
        format_args!("unknown header type: {0}",
            e.header_type)
    },

    UnknownMisbehaviourType
    { misbehavior_type: String }
    | e | {
        format_args!("unknown misbehaviour type: {0}",
            e.misbehavior_type)
    },

    InvalidRawClientId
    { client_id: String }
    [ DisplayError<ValidationError> ]
    | e | {
        format_args!("invalid raw client identifier {0}",
            e.client_id)
    },

    DecodeRawClientState
    [ DisplayError<TendermintError> ]
    | _ | { format_args!("error decoding raw client state") },

    MissingRawClientState
    | _ | { format_args!("missing raw client state") },

    InvalidRawConsensusState
    [ DisplayError<TendermintError> ]
    | _ | { format_args!("invalid raw client consensus state") },

    MissingRawConsensusState
    | _ | { format_args!("missing raw client consensus state") },

    InvalidMsgUpdateClientId
    [ DisplayError<ValidationError> ]
    | _ | { format_args!("invalid client id in the update client message") },

    MissingHeight
    | _ | { format_args!("invalid raw client consensus state: the height field is missing") },

    InvalidClientIdentifier
    [ DisplayError<ValidationError> ]
    | _ | { format_args!("invalid client identifier") },

    InvalidRawHeader
    [ DisplayError<TendermintError> ]
    | _ | { format_args!("invalid raw header") },

    MissingRawHeader
    | _ | { format_args!("missing raw header") },

    DecodeRawMisbehaviour
    [ DisplayError<TendermintError> ]
    | _ | { format_args!("invalid raw misbehaviour") },

    InvalidRawMisbehaviour
    [ DisplayError<ValidationError> ]
    | _ | { format_args!("invalid raw misbehaviour") },

    MissingRawMisbehaviour
    | _ | { format_args!("missing raw misbehaviour") },

    InvalidHeightResult
    | _ | { format_args!("height cannot end up zero or negative") },

    HeightConversion
    { height: String }
    [ DetailOnly<ParseIntError> ]
    | e | {
        format_args!("cannot convert into a `Height` type from string {0}",
            e.height)
    },

    InvalidAddress
    | _ | { format_args!("invalid address") },

    InvalidUpgradeClientProof
    [ DisplayError<Ics23Error> ]
    | _ | { format_args!("invalid proof for the upgraded client state") },

    InvalidUpgradeConsensusStateProof
    [ DisplayError<Ics23Error> ]
    | _ | { format_args!("invalid proof for the upgraded consensus state") },

    InvalidPacketTimestamp
    [ DisplayError<TryFromIntError> ]
    | _ | { format_args!("invalid packet timeout timestamp value") },

    ClientArgsTypeMismatch
    { client_type: ClientType }
    | e | {
        format_args!("mismatch between client and arguments types, expected: {0:?}",
            e.client_type)
    },

    RawClientAndConsensusStateTypesMismatch
    {
        state_type: ClientType,
        consensus_type: ClientType,
    }
    | e | {
        format_args!("mismatch in raw client consensus state {} with expected state {}",
            e.state_type, e.consensus_type)
    },

    UpgradeVerificationFailure
    { reason: String }
    | e | { format_args!("upgrade verification failed with reason: {}", e.reason) },

    LowUpgradeHeight
    {
        upgraded_height: Height,
        client_height: Height,
    }
    | e | {
        format_args!("upgraded client height {0} must be at greater than current client height {1}",
            e.upgraded_height, e.client_height)
    },

}

// pub type Error = anomaly::Error<Kind>;

// #[derive(Clone, Debug, Error, PartialEq, Eq)]
// pub enum Kind {
//     #[error("unknown client type: {0}")]
//     UnknownClientType(String),

//     #[error("Client identifier constructor failed for type {0} with counter {1}")]
//     ClientIdentifierConstructor(ClientType, u64),

//     #[error("client already exists: {0}")]
//     ClientAlreadyExists(ClientId),

//     #[error("client not found: {0}")]
//     ClientNotFound(ClientId),

//     #[error("client is frozen: {0}")]
//     ClientFrozen(ClientId),

//     #[error("consensus state not found at: {0} at height {1}")]
//     ConsensusStateNotFound(ClientId, Height),

//     #[error("implementation specific")]
//     ImplementationSpecific,

//     #[error("header verification failed")]
//     HeaderVerificationFailure,

//     #[error("unknown client state type: {0}")]
//     UnknownClientStateType(String),

//     #[error("the client state was not found")]
//     EmptyClientStateResponse,

//     #[error("unknown client consensus state type: {0}")]
//     UnknownConsensusStateType(String),

//     #[error("the client consensus state was not found")]
//     EmptyConsensusStateResponse,

//     #[error("unknown header type: {0}")]
//     UnknownHeaderType(String),

//     #[error("unknown misbehaviour type: {0}")]
//     UnknownMisbehaviourType(String),

//     #[error("invalid raw client identifier {0} with underlying error: {1}")]
//     InvalidRawClientId(String, ValidationKind),

//     #[error("invalid raw client state")]
//     InvalidRawClientState,

//     #[error("invalid raw client consensus state")]
//     InvalidRawConsensusState,

//     #[error("invalid client id in the update client message")]
//     InvalidMsgUpdateClientId,

//     #[error("invalid raw client consensus state: the height field is missing")]
//     MissingHeight,

//     #[error("invalid client identifier: validation error: {0}")]
//     InvalidClientIdentifier(ValidationKind),

//     #[error("invalid raw header")]
//     InvalidRawHeader,

//     #[error("invalid raw misbehaviour")]
//     InvalidRawMisbehaviour,

//     #[error("invalid height result")]
//     InvalidHeightResult,

//     #[error("cannot convert into a `Height` type from string {0}")]
//     HeightConversion(String, ParseIntError),

//     #[error("invalid address")]
//     InvalidAddress,

//     #[error("invalid proof for the upgraded client state")]
//     InvalidUpgradeClientProof(Ics23Error),

//     #[error("invalid proof for the upgraded consensus state")]
//     InvalidUpgradeConsensusStateProof(Ics23Error),

//     #[error("invalid packet timeout timestamp value")]
//     InvalidPacketTimestamp,

//     #[error("mismatch between client and arguments types, expected: {0:?}")]
//     ClientArgsTypeMismatch(ClientType),

//     #[error("mismatch raw client consensus state")]
//     RawClientAndConsensusStateTypesMismatch {
//         state_type: ClientType,
//         consensus_type: ClientType,
//     },

//     #[error("upgrade verification failed")]
//     UpgradeVerificationFailure,

//     #[error("upgraded client height {0} must be at greater than current client height {1}")]
//     LowUpgradeHeight(Height, Height),
// }

// impl Kind {
//     pub fn context(self, source: impl Into<BoxError>) -> Context<Self> {
//         Context::new(self, Some(source.into()))
//     }
// }
