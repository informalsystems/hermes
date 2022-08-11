use crate::prelude::*;

use flex_error::{define_error, TraceError};

use crate::core::ics23_commitment::error::Error as Ics23Error;
use crate::core::ics24_host::error::ValidationError;
use crate::core::ics24_host::identifier::ClientId;
use crate::timestamp::{Timestamp, TimestampOverflowError};
use codec::Error as ScaleCodecError;

use crate::Height;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidAddress
            |_| { "invalid address" },

        InvalidTrieProof
            |_| { "invalid trie proof" },

        InvalidMmrUpdate
            { reason: String }
            |e| { format_args!("invalid mmr update {}", e.reason) },

        InvalidCommitmentRoot
            |_| { "invalid commitment root" },

        TimestampExtrinsic
            { reason: String }
            |e| { format_args!("error decoding timestamp extrinsic {}", e.reason) },

        InvalidHeader
            { reason: String }
            |e| { format_args!("invalid header, failed basic validation: {}", e.reason) },

        ImplementationSpecific
            { reason: String }
            |e| { format_args!("Implementation specific error: {}", e.reason) },

        Validation
            { reason: String }
            |e| { format_args!("invalid header, failed basic validation: {}", e.reason) },

        InvalidRawClientState
            { reason: String }
            |e| { format_args!("invalid raw client state: {}", e.reason) },

        InvalidChainIdentifier
            [ ValidationError ]
            |_| { "invalid chain identifier" },

        MissingLatestHeight
            |_| { "missing latest height" },

        MissingBeefyAuthoritySet
            |_| { "missing beefy authority set" },

        MissingFrozenHeight
            |_| { "missing frozen height" },

        InvalidChainId
            { raw_value: String }
            [ ValidationError ]
            |e| { format_args!("invalid chain identifier: {}", e.raw_value) },

        InvalidRawHeight
            { raw_height: u64 }
            |e| { format_args!("invalid raw height: {}", e.raw_height) },

        InvalidRawConsensusState
            { reason: String }
            | e | { format_args!("invalid raw client consensus state: {}", e.reason) },

        InvalidRawHeader
            | _ | { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            | e | { format_args!("invalid raw misbehaviour: {}", e.reason) },

        ScaleDecode
            [ TraceError<ScaleCodecError> ]
            | _ | { "Scale decode error" },
        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },

        LowUpdateTimestamp
            {
                low: String,
                high: String
            }
            | e | {
                format_args!("header timestamp {0} must be greater than current client consensus state timestamp {1}", e.low, e.high)
            },

        HeaderTimestampTooHigh
            {
                actual: String,
                max: String,
            }
            | e | {
                format_args!("given other previous updates, header timestamp should be at most {0}, but was {1}", e.max, e.actual)
            },

        HeaderTimestampTooLow
            {
                actual: String,
                min: String,
            }
            | e | {
                format_args!("given other previous updates, header timestamp should be at least {0}, but was {1}", e.min, e.actual)
            },

        TimestampOverflow
            [ TimestampOverflowError ]
            |_| { "timestamp overflowed" },

        NotEnoughTimeElapsed
            {
                current_time: Timestamp,
                earliest_time: Timestamp,
            }
            | e | {
                format_args!("not enough time elapsed, current timestamp {0} is still less than earliest acceptable timestamp {1}", e.current_time, e.earliest_time)
            },

        NotEnoughBlocksElapsed
            {
                current_height: Height,
                earliest_height: Height,
            }
            | e | {
                format_args!("not enough blocks elapsed, current height {0} is still less than earliest acceptable height {1}", e.current_height, e.earliest_height)
            },

        InvalidHeaderHeight
            { height: Height }
            | e | {
                format_args!("header height = {0} is invalid", e.height)
            },

        LowUpdateHeight
            {
                low: Height,
                high: Height
            }
            | e | {
                format_args!("header height is {0} but it must be greater than the current client height which is {1}", e.low, e.high)
            },

        ProcessedTimeNotFound
            {
                client_id: ClientId,
                height: Height,
            }
            | e | {
                format_args!(
                    "Processed time for the client {0} at height {1} not found",
                    e.client_id, e.height)
            },

        ProcessedHeightNotFound
            {
                client_id: ClientId,
                height: Height,
            }
            | e | {
                format_args!(
                    "Processed height for the client {0} at height {1} not found",
                    e.client_id, e.height)
            },


        VerificationError
            { reason: String }
            | e | {
                format_args!("verification failed: {:?}", e.reason)
            },

        Ics23Error
            [ Ics23Error ]
            | _ | { "ics23 commitment error" },

        InsufficientHeight
            {
                latest_height: Height,
                target_height: Height,
            }
            | e | {
                format_args!("the height is insufficient: latest_height={0} target_height={1}", e.latest_height, e.target_height)
            },

        ClientFrozen
            {
                frozen_height: Height,
                target_height: Height,
            }
            | e | {
                format_args!("the client is frozen: frozen_height={0} target_height={1}", e.frozen_height, e.target_height)
            },
        UnknownRelayChain
            { type_id: String }
            | e | { format_args!("Relaychain type not known: {}", e.type_id) },
    }
}
