use flex_error::{define_error, TraceError};
use ibc_proto::ibc::core::client::v1::Height as RawHeight;

use crate::core::ics02_client::error::Error as Ics02Error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        InvalidRawClientState
            { reason: String }
            |e| { format_args!("invalid raw client state: {}", e.reason) },

        MissingLatestHeight
            |_| { "missing latest height" },

        InvalidRawHeight
            { raw_height: RawHeight }
            |e| { format_args!("invalid raw height: {:?}", e.raw_height) },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },
    }
}

impl From<Error> for Ics02Error {
    fn from(e: Error) -> Self {
        Self::client_specific(e.to_string())
    }
}
