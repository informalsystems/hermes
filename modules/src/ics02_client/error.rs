use crate::ics02_client::client_type::ClientType;
use crate::ics23_commitment::error::Error as Ics23Error;
use crate::ics24_host::error::ValidationError;
use crate::ics24_host::identifier::ClientId;
use crate::Height;
use std::num::TryFromIntError;
use tendermint_proto::Error as TendermintError;

use flex_error::{define_error, DisplayOnly};

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        UnknownClientType
            { client_type: String }
            | e | { format_args!("unknown client type: {0}", e.client_type) },

        ClientIdentifierConstructor
            { client_type: ClientType, counter: u64 }
            [ ValidationError ]
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
            | _ | { "implementation specific error" },

        HeaderVerificationFailure
            { reason: String }
            | e | { format_args!("header verification failed with reason: {}", e.reason) },

        UnknownClientStateType
            { client_state_type: String }
            | e | { format_args!("unknown client state type: {0}", e.client_state_type) },

        EmptyClientStateResponse
            | _ | { "the client state was not found" },

        EmptyPrefix
            | _ | { "empty prefix" },

        UnknownConsensusStateType
            { consensus_state_type: String }
            | e | {
                format_args!("unknown client consensus state type: {0}",
                    e.consensus_state_type)
            },

        EmptyConsensusStateResponse
            | _ | { "the client state was not found" },

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
            [ ValidationError ]
            | e | {
                format_args!("invalid raw client identifier {0}",
                    e.client_id)
            },

        DecodeRawClientState
            [ DisplayOnly<TendermintError> ]
            | _ | { "error decoding raw client state" },

        MissingRawClientState
            | _ | { "missing raw client state" },

        InvalidRawConsensusState
            [ DisplayOnly<TendermintError> ]
            | _ | { "invalid raw client consensus state" },

        MissingRawConsensusState
            | _ | { "missing raw client consensus state" },

        InvalidMsgUpdateClientId
            [ ValidationError ]
            | _ | { "invalid client id in the update client message" },

        MissingHeight
            | _ | { "invalid raw client consensus state: the height field is missing" },

        InvalidClientIdentifier
            [ ValidationError ]
            | _ | { "invalid client identifier" },

        InvalidRawHeader
            [ DisplayOnly<TendermintError> ]
            | _ | { "invalid raw header" },

        MissingRawHeader
            | _ | { "missing raw header" },

        DecodeRawMisbehaviour
            [ DisplayOnly<TendermintError> ]
            | _ | { "invalid raw misbehaviour" },

        InvalidRawMisbehaviour
            [ ValidationError ]
            | _ | { "invalid raw misbehaviour" },

        MissingRawMisbehaviour
            | _ | { "missing raw misbehaviour" },

        InvalidHeightResult
            | _ | { "height cannot end up zero or negative" },

        InvalidAddress
            | _ | { "invalid address" },

        InvalidUpgradeClientProof
            [ DisplayOnly<Ics23Error> ]
            | _ | { "invalid proof for the upgraded client state" },

        InvalidUpgradeConsensusStateProof
            [ DisplayOnly<Ics23Error> ]
            | _ | { "invalid proof for the upgraded consensus state" },

        InvalidPacketTimestamp
            [ DisplayOnly<TryFromIntError> ]
            | _ | { "invalid packet timeout timestamp value" },

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

        LowHeaderHeight
            {
                header_height: Height,
                latest_height: Height
            }
            | e | {
                format!("received header height ({:?}) is lower than (or equal to) client latest height ({:?})",
                    e.header_height, e.latest_height)
            },

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
}
