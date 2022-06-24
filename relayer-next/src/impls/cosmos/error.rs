use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use prost::EncodeError;

define_error! {
    Error {
        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Relayer
            [ RelayerError ]
            | _ | { "ibc-relayer error" },

        ForeignClient
            [ ForeignClientError ]
            | _ | { "foreign client error" },

        Encode
            [ TraceError<EncodeError> ]
            | _ | { "protobuf encode error" },
    }
}
