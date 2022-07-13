use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer_framework::impls::packet_relayers::retry::{MaxRetryExceeded, RetryableError};
use ibc_relayer_framework::traits::ibc_message_sender::MismatchIbcEventsCountError;
use prost::EncodeError;

use crate::cosmos::message_senders::batch::{BatchError, ChannelClosedError};

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
            | e | { format_args!("error when sending messages as batches: {}", e.message) }
    }
}

impl RetryableError for Error {
    fn is_retryable(&self) -> bool {
        false
    }
}

impl BatchError for Error {
    fn to_batch_error(&self) -> Self {
        Self::batch(self.to_string())
    }
}

impl From<MismatchIbcEventsCountError> for Error {
    fn from(e: MismatchIbcEventsCountError) -> Error {
        Error::mismatch_ibc_events_count(e.expected, e.actual)
    }
}

impl From<MaxRetryExceeded> for Error {
    fn from(e: MaxRetryExceeded) -> Error {
        Error::max_retry(e.retries)
    }
}

impl From<ChannelClosedError> for Error {
    fn from(_: ChannelClosedError) -> Error {
        Error::channel_closed()
    }
}
