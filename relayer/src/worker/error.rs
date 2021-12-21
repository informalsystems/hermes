use crossbeam_channel::RecvError;
use flex_error::{define_error, DisplayOnly};

use crate::channel::ChannelError;
use crate::connection::ConnectionError;
use crate::link::error::LinkError;
use ibc::core::ics02_client::error::Error as Ics02Error;

define_error! {
    RunError {
        Ics02
            [ Ics02Error ]
            | _ | { "client errror" },

        Connection
            [ ConnectionError ]
            | _ | { "connection errror" },

        Channel
            [ ChannelError ]
            | _ | { "channel errror" },

        Link
            [ LinkError ]
            | _ | { "link errror" },

        Retry
            { retries: retry::Error<u64> }
            | e | {
                format_args!("Worker failed after {} retries",
                    e.retries)
            },

        Recv
            [ DisplayOnly<RecvError> ]
            | _ | { "error receiving from channel: sender end has been closed" }
    }
}

define_error! {
    WorkerError {
        ChannelSend
            { reason: String }
            |e| {
                format_args!("error sending through crossbeam channel: {}",
                    e.reason)
            },
    }
}

impl WorkerError {
    pub fn send<T>(e: crossbeam_channel::SendError<T>) -> WorkerError {
        WorkerError::channel_send(format!("{}", e))
    }
}
