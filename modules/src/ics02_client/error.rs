use flex_error::*;
use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::error::Kind as Ics23Kind;
use crate::ics24_host::error::ValidationKind;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

pub type Error = anyhow::Error;

define_error! {KindError;
    UnknownClientType
    {detail: String}
    [DisplayError<Error>]
    | e | { format_args!("unknown client type: {0}", e.detail) },

    ClientIdentifierConstructor
    {client_type: ClientType, id: u64}
    [DisplayError<Error>]
    | e | { format_args!("Client identifier constructor failed for type {0} with counter {1}", e.client_type, e.id) },

    ClientAlreadyExists
    {client_type: ClientType}
    [DisplayError<Error>]
    | e | { format_args!("client already exists: {0}", e.client_type) },

    ClientNotFound
    {client_type: ClientType}
    [DisplayError<Error>]
    | e | {  format_args!("client not found: {0}", e.client_type) },

    ClientFrozen
    {client_type: ClientType}
    [DisplayError<Error>]
    | e | { format_args!("client is frozen: {0}", e.client_type) },

    ConsensusStateNotFound
    {client_id: ClientId, height: Height}
    [DisplayError<Error>]
    | e | { format_args!("consensus state not found at: {0} at height {1}", e.client_id, e.height) },

    ImplementationSpecific
    [DisplayError<Error>]
    | _ | {  format_args!("implementation specific") },

    NegativeConsensusStateTimestamp
    {detail: String}
    [DisplayError<Error>]
    | e | { format_args!("Negative timestamp in consensus state {0}; timestamp must be a positive value", e.detail)},

    HeaderVerificationFailure
    [DisplayError<Error>]
    | _ | { format_args!("header verification failed")},

    UnknownClientStateType
    {detail : String}
    [DisplayError<Error>]
    | e | { format_args!("unknown client state type: {0}", e.detail)},

    EmptyClientStateResponse
    [DisplayError<Error>]
    | _ | { format_args!("the client state was not found")},

    UnknownConsensusStateType
    { detail: String }
    [DisplayError<Error>]
    | e | { format_args!("unknown client consensus state type: {0}", e.detail) },

    EmptyConsensusStateResponse
    [DisplayError<Error>]
    | _ | { format_args!("the client consensus state was not found") },

    UnknownHeaderType
    {detail: Stirng}
    [DisplayError<Error>]
    | e | { format_args!("unknown header type: {0}", e.detail) },

    UnknownMisbehaviourType
    { detail: String }
    [DisplayError<Error>]
    | e | { format_args!("unknown misbehaviour type: {0}", e.detail) },

    InvalidRawClientState
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw client state") },

    InvalidRawConsensusState
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw client consensus state") },

    InvalidClientIdentifier
    {validation_kind: ValidationKind}
    [DisplayError<Error>]
    | e | { format_args!("invalid client identifier: validation error: {0}", e.validation_kind) },

    InvalidRawHeader
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw header") },

    InvalidRawMisbehaviour
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw misbehaviour") },

    InvalidHeightResult
    [DisplayError<Error>]
    | _ | { format_args!("invalid height result") },

    InvalidAddress
    [DisplayError<Error>]
    | _ | { format_args!("invalid address") },

    InvalidUpgradeClientProof
    { ics23kind: Ics23Kind }
    [DisplayError<Error>]
    | _ | { format_args!("invalid proof for the upgraded client state") },

    InvalidUpgradeConsensusStateProof
    {ics23kind: Ics23Kind}
    [DisplayError<Error>]
    | _ | { format_args!("invalid proof for the upgraded consensus state") },

    ClientArgsTypeMismatch
    {client_type: ClientType}
    [DisplayError<Error>]
    | e | { format_args!("mismatch between client and arguments types, expected: {0:?}", e.client_type) },

    RawClientAndConsensusStateTypesMismatch
    {state_type: ClientType, consensus_type: CLientType}
    [DisplayError<Error>]
    | _ | { format_args!("mismatch raw client consensus state") },
}
