use crate::prelude::*;

use flex_error::{define_error, TraceError};

use crate::ics24_host::error::ValidationError;
use crate::Height;
use tendermint::account::Id;
use tendermint::hash::Hash;
use tendermint::Error as TendermintError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidTrustingPeriod
            { reason: String }
            |e| { format_args!("invalid trusting period: {}", e.reason) },

        InvalidUnbondingPeriod
            { reason: String }
            |e| { format_args!("invalid unbonding period: {}", e.reason) },

        InvalidAddress
            |_| { "invalid address" },

        InvalidHeader
            { reason: String }
            [ TendermintError ]
            |e| { format_args!("invalid header, failed basic validation: {}", e.reason) },

        InvalidTrustThreshold
            { reason: String }
            |e| { format_args!("invalid client state trust threshold: {}", e.reason) },

        MissingSignedHeader
            |_| { "missing signed header" },

        Validation
            { reason: String }
            |e| { format_args!("invalid header, failed basic validation: {}", e.reason) },

        InvalidRawClientState
            { reason: String }
            |e| { format_args!("invalid raw client state: {}", e.reason) },

        MissingValidatorSet
            |_| { "missing validator set" },

        MissingTrustedValidatorSet
            |_| { "missing trusted validator set" },

        MissingTrustedHeight
            |_| { "missing trusted height" },

        MissingTrustingPeriod
            |_| { "missing trusting period" },

        MissingUnbondingPeriod
            |_| { "missing unbonding period" },

        InvalidChainIdentifier
            [ ValidationError ]
            |_| { "invalid chain identifier" },

        NegativeTrustingPeriod
            |_| { "negative trusting period" },

        NegativeUnbondingPeriod
            |_| { "negative unbonding period" },

        MissingMaxClockDrift
            |_| { "missing max clock drift" },

        NegativeMaxClockDrift
            |_| {  "negative max clock drift" },

        MissingLatestHeight
            |_| { "missing latest height" },

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
            [ TendermintError ]
            | _ | { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            | e | { format_args!("invalid raw misbehaviour: {}", e.reason) },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },

        InsufficientVotingPower
            { reason: String }
            | e | {
                format_args!("insufficient overlap: {}", e.reason)
            },

        LowUpdateTimestamp
            {
                low: String,
                high: String
            }
            | e | {
                format_args!("header timestamp {0} must be greater than current client consensus state timestamp {1}", e.low, e.high)
            },

        HeaderTimestampOutsideTrustingTime
            {
                low: String,
                high: String
            }
            | e | {
                format_args!("header timestamp {0} is outside the trusting period w.r.t. consensus state timestamp {1}", e.low, e.high)
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

        InvalidHeaderHeight
            { height: Height }
            | e | {
                format_args!("header height = {0} is invalid", e.height)
            },

        InvalidTrustedHeaderHeight
            {
                trusted_header_height: Height,
                height_header: Height
            }
            | e | {
                format_args!("header height is {0} and is lower than the trusted header height, which is {1} ", e.height_header, e.trusted_header_height)
            },

        LowUpdateHeight
            {
                low: Height,
                high: Height
            }
            | e | {
                format_args!("header height is {0} but it must be greater than the current client height which is {1}", e.low, e.high)
            },

        MismatchedRevisions
            {
                current_revision: u64,
                update_revision: u64,
            }
            | e | {
                format_args!("the header's current/trusted revision number ({0}) and the update's revision number ({1}) should be the same", e.current_revision, e.update_revision)
            },

        InvalidValidatorSet
            {
                hash1: Hash,
                hash2: Hash,
            }
            | e | {
                format_args!("invalid validator set: header_validators_hash={} and validators_hash={}", e.hash1, e.hash2)
            },

        NotEnoughTrustedValsSigned
            { reason: String }
            | e | {
                format_args!("not enough trust because insufficient validators overlap: {}", e.reason)
            },

        VerificationError
            { detail: tendermint_light_client::predicates::errors::VerificationErrorDetail }
            | e | {
                format_args!("verification failed: {}", e.detail)
            }
    }
}

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    VerificationError {
        InvalidSignature
            | _ | { "couldn't verify validator signature" },

        DuplicateValidator
            { id: Id }
            | e | {
                format_args!("duplicate validator in commit signatures with address {}", e.id)
            },

        InsufficientOverlap
            { q1: u64, q2: u64 }
            | e | {
                format_args!("insufficient signers overlap between {0} and {1}", e.q1, e.q2)
            },
    }
}
