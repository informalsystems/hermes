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

        ProtoEncode
            [ TraceError<prost::EncodeError> ]
            | _ | { "Protobuf encoding error error" },

        ProtoDecode
            [ TraceError<prost::DecodeError> ]
            | _ | { "Protbuf decoding error" },

        Ics02
            [ Ics02Error ]
            | _ | { "ICS 002 error" },
    }
}

impl From<prost::EncodeError> for Error {
    fn from(e: prost::EncodeError) -> Self {
        Self::proto_encode(e)
    }
}

impl From<prost::DecodeError> for Error {
    fn from(e: prost::DecodeError) -> Self {
        Self::proto_decode(e)
    }
}

impl From<Error> for Ics02Error {
    fn from(e: Error) -> Self {
        Self::client_specific(e.to_string())
    }
}

impl From<Ics02Error> for Error {
    fn from(e: Ics02Error) -> Self {
        Self::ics02(e)
    }
}
