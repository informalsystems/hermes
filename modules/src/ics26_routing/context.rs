use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use crate::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::ics05_port::context::PortReader;
/// This trait captures all the functional dependencies (i.e., context) which the ICS26 module
/// requires to be able to dispatch and process IBC messages. In other words, this is the
/// representation of a chain from the perspective of the IBC module of that chain.
pub trait ICS26Context:
    ClientReader
    + ClientKeeper
    + ConnectionReader
    + ConnectionKeeper
    + ChannelKeeper
    + ChannelReader
    + PortReader
    + Clone
{
}
