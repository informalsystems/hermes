use crate::application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use crate::ics02_client::msgs::ClientMsg;
use crate::ics04_channel::msgs::ChannelMsg;
use crate::{ics03_connection::msgs::ConnectionMsg, ics04_channel::msgs::PacketMsg};

/// Enumeration of all messages that the local ICS26 module is capable of routing.
#[derive(Clone, Debug)]
pub enum Ics26Envelope {
    Ics2Msg(ClientMsg),
    Ics3Msg(ConnectionMsg),
    Ics4ChannelMsg(ChannelMsg),
    Ics4PacketMsg(PacketMsg),
    Ics20Msg(MsgTransfer),
}
