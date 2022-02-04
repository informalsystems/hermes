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
            | _ | { "client error" },

        Connection
            [ ConnectionError ]
            | _ | { "connection error" },

        Channel
            [ ChannelError ]
            | _ | { "channel error" },

        Link
            [ LinkError ]
            | _ | { "link error" },

        Retry
            { retries: retry::Error<u64> }
            | e | { format_args!("worker failed after {} retries", e.retries) },

        Recv
            [ DisplayOnly<RecvError> ]
            | _ | { "error receiving from channel: sender end has been closed" }
    }
}
