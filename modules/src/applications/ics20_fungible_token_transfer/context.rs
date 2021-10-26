use crate::core::ics04_channel::context::{ChannelKeeper, ChannelReader};

/// Captures all the dependencies which the ICS20 module requires to be able to dispatch and
/// process IBC messages.
pub trait Ics20Context: ChannelReader + ChannelKeeper + Clone {}
