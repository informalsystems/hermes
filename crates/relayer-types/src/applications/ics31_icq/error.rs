use crate::core::ics24_host::error::ValidationError as Ics24ValidationError;
use cometbft::error::Error as CometbftError;

use flex_error::define_error;

define_error! {
    Error {
        Parse
            | _ | { "Failed to parse content" },

        Event
            { event: String }
            | e | { format!("Event attribute not found: {}", e.event) },

        Ics24
            { error: Ics24ValidationError }
            | e | { format!("ics24 validation error: {:?}", e.error) },

        Cometbft
            { error: CometbftError }
            | e | { format!("CometBFT error: {:?}", e.error) },

        Query
            | _ | { "Failed to query data" },

        Proof
            | _ | { "Proof not found" },

        ProtoEncode
            | _ | { "Failed to encode interchain query Protobuf" },
    }
}

impl From<Ics24ValidationError> for Error {
    fn from(e: Ics24ValidationError) -> Self {
        Self::ics24(e)
    }
}

impl From<CometbftError> for Error {
    fn from(e: CometbftError) -> Self {
        Self::cometbft(e)
    }
}
