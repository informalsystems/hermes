use super::types::CryptoHash;
use flex_error::define_error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidEpoch
        { epoch_id: CryptoHash }
        | _ | { "invalid epoch id" },
        HeightTooOld
        | e | { format_args!(
            "height too old")
        },
        InvalidSignature
        | e | { format_args!(
            "invalid signature")
        },
        InsufficientStakedAmount
        | e | { format_args!(
            "insufficient staked amount")
        },
        SerializationError
        | e | { format_args!(
            "serialization error")
        },
        UnavailableBlockProducers
        | e | { format_args!(
            "unavailable block producers")
        },
    }
}
