use crate::ics02_client::msgs::ClientMsg;
use crate::ics03_connection::msgs::ConnectionMsg;
use crate::ics04_channel::msgs::ChannelMsg;

/// Enumeration of all messages that the local ICS26 module is capable of routing.
#[derive(Clone, Debug)]
pub enum Ics26Envelope {
    Ics2Msg(ClientMsg),
    Ics3Msg(ConnectionMsg),
    Ics4Msg(ChannelMsg),
}
