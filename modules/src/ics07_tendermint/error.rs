use crate::prelude::*;

use flex_error::{define_error, TraceError};

use crate::ics24_host::error::ValidationError;

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
            | _ | { "invalid address" },

        InvalidHeader
            { reason: String }
            [ tendermint::Error ]
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
            |e| { format_args!("invalid raw client consensus state: {}", e.reason) },

        InvalidRawHeader
            [ tendermint::Error ]
            |_| { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            |e| { format_args!("invalid raw misbehaviour: {}", e.reason) },

        Decode
            [ TraceError<prost::DecodeError> ]
            |_| { "decode error" },
    }
}
