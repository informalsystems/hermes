use crate::ics02_client::msgs::ClientMsg;
use crate::ics03_connection::msgs::ConnectionMsg;
use crate::ics04_channel::msgs::ChannelMsg;

/// Enumeration of all messages that the local ICS26 module is capable of routing.
#[derive(Clone, Debug)]
pub enum ICS26Envelope {
    ICS2Msg(ClientMsg),
    ICS3Msg(ConnectionMsg),
    ICS4Msg(ChannelMsg),
}
