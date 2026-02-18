use flex_error::{define_error, TraceError};

use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics24_host::error::ValidationError;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        MissingField
            { field: &'static str }
            |e| { format_args!("missing required field: {}", e.field) },

        InvalidField
            { field: &'static str, reason: String }
            |e| { format_args!("invalid field {}: {}", e.field, e.reason) },

        InvalidHeight
            { height: u64 }
            |e| { format_args!("invalid Mithril header height: {}", e.height) },

        InvalidTimestamp
            { value: String }
            |e| { format_args!("invalid Mithril header timestamp: {}", e.value) },

        Decode
            [ TraceError<prost::DecodeError> ]
            |_| { "decode error" },

        InvalidChainId
            { value: String }
            [ ValidationError ]
            |e| { format_args!("invalid chain id: {}", e.value) },

        HeightConversion
            { reason: String }
            |e| { format_args!("height conversion error: {}", e.reason) },

        TimestampConversion
            { reason: String }
            |e| { format_args!("timestamp conversion error: {}", e.reason) },
    }
}

impl From<Error> for Ics02Error {
    fn from(e: Error) -> Self {
        Self::client_specific(e.to_string())
    }
}
