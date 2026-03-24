use flex_error::{define_error, TraceError};

use crate::core::ics02_client::error::Error as Ics02Error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidHeader
            { reason: String }
            |e| { format_args!("invalid Stellar header: {}", e.reason) },

        InvalidRawClientState
            { reason: String }
            |e| { format_args!("invalid raw Stellar client state: {}", e.reason) },

        InvalidRawConsensusState
            { reason: String }
            |e| { format_args!("invalid raw Stellar consensus state: {}", e.reason) },

        InvalidRawMisbehaviour
            { reason: String }
            |e| { format_args!("invalid raw Stellar misbehaviour: {}", e.reason) },

        Decode
            [ TraceError<prost::DecodeError> ]
            |_| { "decode error" },
    }
}

impl From<Error> for Ics02Error {
    fn from(e: Error) -> Self {
        Self::client_specific(e.to_string())
    }
}
