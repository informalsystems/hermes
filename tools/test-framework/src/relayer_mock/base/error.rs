use eyre::Report;
use flex_error::{define_error, TraceError};

use ibc_relayer_runtime::tokio::error::Error as TokioError;

define_error! {
    #[derive(Clone, Debug)]
    Error {
        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Tokio
            [ TokioError ]
            | _ | { "tokio runtime error" },

        MismatchError
            { expected: usize, actual: usize }
            | e | {
                format_args!("mismatch size for events returned. expected: {}, got: {}",
                    e.expected, e.actual)
            },
        NoConsensusState
        { client_id: String }
            | e | {
                format_args!("no consensus state found for client id: {}", e.client_id)
            },
    }
}

impl From<TokioError> for Error {
    fn from(e: TokioError) -> Error {
        Error::tokio(e)
    }
}
