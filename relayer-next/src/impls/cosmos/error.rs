use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use prost::EncodeError;

use crate::traits::ibc_message_sender::MismatchIbcEventsCountError;

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

        MismatchIbcEventsCount
            { expected: usize, actual: usize }
            | e | {
                format_args!("mismatch size for events returned. expected: {}, got: {}",
                    e.expected, e.actual)
            }
    }
}

impl From<MismatchIbcEventsCountError> for Error {
    fn from(e: MismatchIbcEventsCountError) -> Error {
        Error::mismatch_ibc_events_count(e.expected, e.actual)
    }
}
