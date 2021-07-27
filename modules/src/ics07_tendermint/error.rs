use crate::ics24_host::error::ValidationError;
use flex_error::{define_error, DisplayOnly, TraceError};
use std::fmt::Display;

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
            { reason: String }
            [ DisplayOnly<LegacyError> ]
            | _ | { "invalid header, failed basic validation" },

        InvalidTrustThreshold
            { reason: String }
            | e | {
                format_args!("invalid client state trust threshold: {}",
                    e.reason)
            },

        MissingSignedHeader
            | _ | { "missing signed header" },

        Validation
            { reason: String }
            | _ | { "invalid header, failed basic validation" },

        InvalidRawClientState
            { reason: String }
            | _ | { "invalid raw client state" },

        MissingValidatorSet
            | _ | { "missing validator set" },

        MissingTrustedValidatorSet
            | _ | { "missing trusted validator set" },

        MissingTrustedHeight
            | _ | { "missing trusted height" },

        MissingTrustingPeriod
            | _ | { "missing trusting period" },

        MissingUnbondingPeriod
            | _ | { "missing unbonding period" },

        InvalidChainIdentifier
            [ ValidationError ]
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
            { raw_value: String }
            [ ValidationError ]
            | e | { format_args!("invalid chain identifier: raw value {0}", e.raw_value) },

        InvalidRawHeight
            | _ | { "invalid raw height" },

        InvalidRawConsensusState
            { reason: String }
            | _ | { "invalid raw client consensus state" },

        InvalidRawHeader
            [ DisplayOnly<LegacyError> ]
            | _ | { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            | _ | { "invalid raw misbehaviour" },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },

    }
}

pub struct LegacyError {
    #[cfg(feature = "std_err")]
    pub error: Box<dyn std::error::Error + Send + Sync>,

    #[cfg(not(feature = "std_err"))]
    pub error: String,
}

impl Display for LegacyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "LegacyError: {}", self.to_string())
    }
}

#[cfg(feature = "std_err")]
impl From<Box<dyn std::error::Error + Send + Sync>> for LegacyError {
    fn from(value: Box<dyn std::error::Error + Send + Sync>) -> Self {
        Self { error: value }
    }
}

#[cfg(not(feature = "std_err"))]
impl From<String> for LegacyError {
    fn from(value: String) -> Self {
        Self { error: value }
    }
}
