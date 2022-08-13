use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc::core::ics04_channel::error::Error as ChannelError;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use prost::EncodeError;

use crate::cosmos::message_senders::batch::{BatchError, ChannelClosedError};

define_error! {
    Error {
        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Channel
            [ ChannelError ]
            | _ | { "channel error" },

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
            },

        MismatchConsensusState
            | _ | { "consensus state of a cosmos chain on the counterparty chain must be a tendermint consensus state" },

        MaxRetry
            { retries: usize }
            | e | { format_args!("max retries exceeded after trying for {} time", e.retries) },

        ChannelClosed
            | _ | { "unexpected closure of internal rust channels" },

        Batch
            { message: String }
            | e | { format_args!("error when sending messages as batches: {}", e.message) },

        MismatchEventType
            { expected: String, actual: String }
            | e | { format_args!("mismatch event type, expected: {}, actual: {}", e.expected, e.actual) },
    }
}

impl BatchError for Error {
    fn to_batch_error(&self) -> Self {
        Self::batch(self.to_string())
    }
}

impl From<ChannelClosedError> for Error {
    fn from(_: ChannelClosedError) -> Error {
        Error::channel_closed()
    }
}
