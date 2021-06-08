use crate::ics24_host::identifier::{ChannelId, PortId};
use flex_error::*;
use std::string::String;

pub type Error = anyhow::Error;

define_error! { FungibleTokenTransferError;
    UnknownMessageTypeUrl
    {detail: String}
    | e | { format_args!("unrecognized ICS-20 transfer message type URL {0}", e.detail) },

    HandlerRaised
    | _ | { format_args!("error raised by message handler") },

    SequenceSendNotFound
    {prot_id: PortId, channel_id: ChannelId}
    | e | { format_args!("Sending sequence number not found for port {0} and channel {1}", e.prot_id, e.channel_id) },

    ChannelNotFound
    {prot_id: PortId, channel_id: ChannelId}
    | e | { format_args!("Missing channel for port_id {0} and channel_id {1}", e.prot_id, e.channel_id) },

    DestinationChannelNotFound
    {prot_id: PortId, channel_id: ChannelId}
    | e | { format_args!("Destination channel not found in the counterparty of port_id {0} and channel_id {1}", e.prot_id, e.channel_id) },
}
