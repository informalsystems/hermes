use flex_error::*;
use std::string::String;

use crate::ics24_host::error::ValidationKind;

pub type Error = anyhow::Error;

define_error! { TendermintError;

    InvalidTrustingPeriod
    [DisplayError<Error>]
    | _ | { format_args!("invalid trusting period")},

    InvalidUnboundingPeriod
    [DisplayError<Error>]
    | _ | { format_args!("invalid unbonding period")},

    InvalidAddress
    | _ | { format_args!("invalid address")},

    InvalidHeader
        [DisplayError<Error>]
    | _ | { format_args!("invalid header, failed basic validation")},

    Validation
    [DisplayError<Error>]
    | _ | { format_args!("validation error")},

    InvalidRawClientState
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw client state")},

    InvalidChainId
    {value: String, validation_kind: ValidationKind}
    | e | { format_args!("invalid chain identifier: raw value {0} with underlying validation error: {1}", e.value, e.validation_kind)},

    InvalidRawHeight
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw height")},

    InvalidRawConsensusState
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw client consensus state")},

    InvalidRawHeader
        [DisplayError<Error>]
    | _ | { format_args!("invalid raw header")},

    InvalidRawMisbehaviour
    [DisplayError<Error>]
    | _ | { format_args!("invalid raw misbehaviour")},
}
