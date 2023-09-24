use crate::core::ics02_client::error::Error as Ics02Error;
use crate::timestamp::ParseTimestampError;
use flex_error::{define_error, TraceError};

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Solomachine
            |_| { "solomachine" },
        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "decode error" },

        ParseTimestampError
            [ParseTimestampError]
            | _ | { "parse timestamp error"},

        ConsensusStateIsEmpty
            | _ | { "consensus state is empty!"},

        PublicKeyIsEmpty
            | _ | { "public key is emoty!" },

        PublicKeyParseFailed
            [ TraceError<eyre::Report> ]
            | _ | { "public key parse failed" },

        InvalidHeight
            [ TraceError<Ics02Error> ]
            | _ | { "invalid ibc height" }

    }
}

impl From<Error> for Ics02Error {
    fn from(e: Error) -> Self {
        Self::client_specific(e.to_string())
    }
}
