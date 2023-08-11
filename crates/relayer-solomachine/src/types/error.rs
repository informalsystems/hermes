use alloc::sync::Arc;
use eyre::Report;
use flex_error::define_error;
use flex_error::TraceError;
use prost::EncodeError;

use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_types::core::ics03_connection::connection::State as ConnectionState;
use ibc_relayer_types::core::ics04_channel::channel::State as ChannelState;

pub type Error = Arc<BaseError>;

define_error! {
    #[derive(Clone, Debug)]
    BaseError {
        Encode
            [ TraceError<EncodeError> ]
            | _ | { "protobuf encode error" },

        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        InvalidChannelState
            { expected: ChannelState, actual: ChannelState }
            | e | { format_args!("channel state error, expected {} got {}", e.expected, e.actual) },

        InvalidConnectionState
            { expected: ConnectionState, actual: ConnectionState }
            | e | { format_args!("connection state error, expected {} got {}", e.expected, e.actual) },

        Tokio
            [ TokioError ]
            | _ | { "tokio runtime error" },
    }
}

impl From<Report> for BaseError {
    fn from(e: Report) -> Self {
        BaseError::generic(e)
    }
}
