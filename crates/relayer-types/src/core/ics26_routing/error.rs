use crate::prelude::*;
use flex_error::{define_error, TraceError};

use crate::applications::transfer;
use crate::core::ics02_client;
use crate::core::ics03_connection;
use crate::core::ics04_channel;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Ics02Client
            [ ics02_client::error::Error ]
            | _ | { "ICS02 client error" },

        Ics03Connection
            [ ics03_connection::error::Error ]
            | _ | { "ICS03 connection error" },

        Ics04Channel
            [ ics04_channel::error::Error ]
            | _ | { "ICS04 channel error" },

        Ics20FungibleTokenTransfer
            [ transfer::error::Error ]
            | _ | { "ICS20 fungible token transfer error" },

        UnknownMessageTypeUrl
            { url: String }
            | e | { format_args!("unknown type URL {0}", e.url) },

        MalformedMessageBytes
            [ TraceError<ibc_proto::protobuf::Error> ]
            | _ | { "the message is malformed and cannot be decoded" },
    }
}
