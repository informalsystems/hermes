use crossbeam_channel::RecvError;
use flex_error::{define_error, DisplayOnly};
use ibc_relayer_types::applications::ics31_icq::error::Error as Ics31Error;
use ibc_relayer_types::core::ics02_client::error::Error as Ics02Error;

use crate::channel::ChannelError;
use crate::connection::ConnectionError;
use crate::error::Error as RelayerError;
use crate::foreign_client::ForeignClientError;
use crate::link::error::LinkError;

define_error! {
    RunError {
        Ics02
            [ Ics02Error ]
            | _ | { "client error" },

        Ics31
            [ Ics31Error ]
            | _ | { "cross chain query error" },

        Connection
            [ ConnectionError ]
            | _ | { "connection error" },

        Channel
            [ ChannelError ]
            | _ | { "channel error" },

        ForeignClient
            [ ForeignClientError ]
            | _ | { "foreign client error" },

        Link
            [ LinkError ]
            | _ | { "link error" },

        Relayer
            [ RelayerError ]
            | _ | { "relayer error" },

        Retry
            { retries: retry::Error<u64> }
            | e | { format_args!("worker failed after {} retries", e.retries) },

        Recv
            [ DisplayOnly<RecvError> ]
            | _ | { "error receiving from channel: sender end has been closed" },
    }
}
