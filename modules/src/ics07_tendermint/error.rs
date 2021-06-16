use crate::ics24_host::error::ValidationError;
use flex_error::*;

define_error! {
    Error {
        InvalidTrustingPeriod
            { reason: String }
            | _ | { "invalid trusting period" },

        InvalidUnboundingPeriod
            { reason: String }
            | _ | { "invalid unbonding period" },

        InvalidAddress
            | _ | { "invalid address" },

        InvalidHeader
            {reason: String }
            | _ | { "invalid header, failed basic validation" },

        Validation
            { reason: String }
            | _ | { "invalid header, failed basic validation" },

        InvalidRawClientState
            {reason: String }
            | _ | { "invalid raw client state" },

        MissingTrustingPeriod
            | _ | { "missing trusting period" },

        MissingUnbondingPeriod
            | _ | { "missing unbonding period" },

        InvalidChainIdentifier
            | _ | { "Invalid chain identifier" },

        NegativeTrustingPeriod
            | _ | { "negative trusting period" },

        NegativeUnbondingPeriod
            | _ | { "negative unbonding period" },

        MissingMaxClockDrift
            | _ | { "missing max clock drift" },

        NegativeMaxClockDrift
            | _ | {  "negative max clock drift" },

        MissingLatestHeight
            | _ | { "missing latest height" },

        MissingFrozenHeight
            | _ | { "missing frozen height" },

        InvalidChainId
            {raw_value: String, validation_kind: ValidationError}
            | e | { format_args!("invalid chain identifier: raw value {0} with underlying validation error: {1}", e.raw_value, e.validation_kind) },

        InvalidRawHeight
            | _ | { "invalid raw height" },

        InvalidRawConsensusState
            {reason: String }
            | _ | { "invalid raw client consensus state" },

        InvalidRawHeader
            {reason: String }
            | _ | { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            | _ | { "invalid raw misbehaviour" },
    }
}