use alloc::string::FromUtf8Error;
use core::num::ParseIntError;

use crate::core::ics04_channel::error as channel_error;
use crate::core::ics24_host::error::ValidationError;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

use flex_error::{define_error, DisplayOnly, TraceError};

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        UnknowMessageTypeUrl
            { url: String }
            | e | { format_args!("unrecognized ICS-20 transfer message type URL {0}", e.url) },

        Ics04Channel
            [ channel_error::Error ]
            |_ | { "Ics04 channel error" },

        DestinationChannelNotFound
            { port_id: PortId, channel_id: ChannelId }
            | e | { format_args!("destination channel not found in the counterparty of port_id {0} and channel_id {1} ", e.port_id, e.channel_id) },

        InvalidPortId
            { context: String }
            [ ValidationError ]
            | _ | { "invalid port identifier" },

        InvalidChannelId
            { context: String }
            [ ValidationError ]
            | _ | { "invalid channel identifier" },

        InvalidPacketTimeoutHeight
            { context: String }
            | _ | { "invalid packet timeout height value" },

        InvalidPacketTimeoutTimestamp
            { timestamp: u64 }
            | _ | { "invalid packet timeout timestamp value" },

        Utf8
            [ DisplayOnly<FromUtf8Error> ]
            | _ | { "utf8 decoding error" },

        EmptyBaseDenom
            |_| { "base denomination is empty" },

        InvalidBaseDenom
            |_| { "invalid characters in base denomination" },

        InvalidTracePortId
            { pos: usize }
            [ ValidationError ]
            | e | { format_args!("invalid port id in trace at position: {0}", e.pos) },

        InvalidTraceChannelId
            { pos: usize }
            [ ValidationError ]
            | e | { format_args!("invalid channel id in trace at position: {0}", e.pos) },

        InvalidTraceLength
            { len: usize }
            | e | { format_args!("trace length must be even but got: {0}", e.len) },

        InvalidCoinAmount
            [ TraceError<ParseIntError> ]
            | _ | { "invalid coin amount" },
    }
}
