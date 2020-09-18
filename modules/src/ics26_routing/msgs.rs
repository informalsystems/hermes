use crate::ics02_client::msgs::ClientMsg;
use crate::ics03_connection::msgs::ConnectionMsg;

/// Enumeration of all possible messages that the ICS26 module can route
#[derive(Clone, Debug)]
pub enum ICS26RoutedMsgs {
    ICS2Msg(ClientMsg),
    ICS3Msg(ConnectionMsg),
}
