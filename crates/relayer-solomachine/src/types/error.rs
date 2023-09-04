use alloc::sync::Arc;
use eyre::Report;
use flex_error::define_error;
use flex_error::TraceError;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use prost::EncodeError;

use ibc_relayer_cosmos::types::error::Error as CosmosError;
use ibc_relayer_runtime::tokio::error::Error as TokioError;
use ibc_relayer_types::core::ics03_connection::connection::State as ConnectionState;
use ibc_relayer_types::core::ics04_channel::channel::State as ChannelState;

pub type Error = Arc<BaseError>;

define_error! {
    #[derive(Clone, Debug)]
    BaseError {
        CosmosChainError
            [ TraceError<CosmosError> ]
            | _ | { "cosmos chain error" },


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

        MissingClientState
            { client_id: ClientId }
            | e | { format_args!("client state for client id `{}` was not found", e.client_id) },

        MissingConnectionEnd
            { connection_id: ConnectionId }
            | e | { format_args!("connection end for connection id `{}` was not found", e.connection_id) },

        MissingConsensusState
            { client_id: ClientId }
            | e | { format_args!("consensus state for client id `{}` was not found", e.client_id) },

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
