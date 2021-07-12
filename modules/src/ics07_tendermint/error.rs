use crate::ics24_host::error::ValidationError;
use flex_error::{define_error, DisplayOnly, TraceError};
use std::fmt::Display;

#[derive(Debug)]
pub struct StdError {
    inner: Box<dyn std::error::Error + Send + Sync>,
}

impl StdError {
    pub fn new(value: Box<dyn std::error::Error + Send + Sync>) -> Self  {
        Self {
            inner: value
        }
    }

}

impl From<String> for StdError {
    fn from(value: String) -> Self {
        Self {
            inner: value.into()
        }
    }
}

#[derive(Debug)]
pub enum LegacyError {
    InnerBox(StdError),
    #[cfg(feature = "test_no_std")]
    InnerString(String),
}

impl LegacyError {
    fn as_str(&self) -> String {
        match self {
            LegacyError::InnerBox(val) => {
                val.inner.to_string()
            }
            #[cfg(feature = "test_no_std")]
            LegacyError::InnerString(val) => {
                val.clone()
            }
        }
    }
}

impl Display for LegacyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "LegacyError: {}", self.as_str())
    }
}

// #[cfg(feature = "std")]
impl From<Box<dyn std::error::Error + Send + Sync>> for LegacyError {
    fn from(value: Box<dyn std::error::Error + Send + Sync>) -> Self {
        LegacyError::InnerBox(StdError::new(value))
    }

}

#[cfg(feature = "test_no_std")]
impl From<Box<dyn std::error::Error + Send + Sync>> for LegacyError {
    fn from(value: Box<dyn std::error::Error + Send + Sync>) -> Self {
        LegacyError::InnerString(value.to_string())
    }
}

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
