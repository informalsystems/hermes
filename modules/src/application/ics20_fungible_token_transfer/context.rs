use crate::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::ics05_port::context::PortReader;

/// Captures all the dependencies which the ICS20 module requires to be able to dispatch and
/// process IBC messages.
pub trait Ics20Context: ChannelReader + ChannelKeeper + PortReader + Clone {}
