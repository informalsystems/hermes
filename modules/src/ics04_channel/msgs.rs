//! Message definitions for all ICS4 domain types: channel open & close handshake datagrams, as well
//! as packets.

use crate::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use crate::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use crate::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;

// Opening handshake messages.
pub mod chan_open_ack;
pub mod chan_open_confirm;
pub mod chan_open_init;
pub mod chan_open_try;

// Closing handshake messages.
pub mod chan_close_confirm;
pub mod chan_close_init;

// Packet specific messages.
pub mod acknowledgement;
pub mod recv_packet;
pub mod timeout;

/// Enumeration of all possible messages that the ICS4 protocol processes.
#[derive(Clone, Debug, PartialEq)]
pub enum ChannelMsg {
    ChannelOpenInit(MsgChannelOpenInit),
    ChannelOpenTry(Box<MsgChannelOpenTry>),
    ChannelOpenAck(Box<MsgChannelOpenAck>),
    ChannelOpenConfirm(MsgChannelOpenConfirm),
}
