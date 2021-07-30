use crate::Height;
use tendermint::{account::Id, validator::Info};
use crate::ics24_host::error::ValidationError;
use flex_error::{define_error, DisplayOnly, TraceError};

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
            [ DisplayOnly<Box<dyn std::error::Error + Send + Sync>> ]
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
            [ DisplayOnly<Box<dyn std::error::Error + Send + Sync>> ]
            | _ | { "invalid raw header" },

        InvalidRawMisbehaviour
            { reason: String }
            | _ | { "invalid raw misbehaviour" },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },
        
        InsufficientVotingPower
                [String]
            | _ |{
                format_args!("Insufficient overlap")
            },

        LowUpdateTimestamp
        {
            low:String, 
            high: String
        }
            |e|{
                format_args!("Hearder timestamp {0} must be at 
                greater than current client consensus state timestamp {1}",e.low,e.high)
            },

        HeaderTimestampOutsideTrustingTime
            {
                low:String, 
                high: String
            }
            |e|{
                format_args!("Header timestamp {0} is outside the trusting period w.r.t. consenus state timestamp{1}",e.low,e.high)
            },
    
        InvalidHeaderHeight
            {
                height: Height
            }
                |e|{
                    format_args!("Header height = {0} is invalid",e.height)
                },

        LowUpdateHeight
            {
                low: Height,
                high: Height
            }
            |e|{
                format_args!("Header height {0} must be at greater than current client height {1}",e.low,e.high)
            },
    }
}

// define_error! {
//      VerificationError {
//         InvalidSignature {
//             /// Signature as a byte array
//             signature: Vec<u8>,
//             /// Validator which provided the signature
//             validator: Box<Info>,
//             /// Bytes which were signed
//             sign_bytes: Vec<u8>,
//         }{
//             | e |{format_args!("Couldn't verify signature 
//             {0} with validator 
//             {1} on sign_bytes 
//             {2}"),e.signature, e.validator, e.sign_bytes}
//         },
    
//         // /// Duplicate validator in commit signatures
//         // #[error("duplicate validator with address {0}")]
//         // DuplicateValidator(Id),
    
//         // /// Insufficient signers overlap
//         // #[error("insufficient signers overlap {0} {1}")]
//         // InsufficientOverlap(u64, u64),
// }
// }
