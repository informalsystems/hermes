use crate::ics04_channel::context::{ChannelKeeper, ChannelReader};
use crate::ics05_port::context::PortReader;
/// This trait captures all the functional dependencies (i.e., context)
/// that the module ICS20 has from the application but also from the ICS26 module
/// It requires to be able to dispatch and process certain IBC messages.
/// In other words, this is the
/// representation of a chain from the perspective of the IBC20 of that chain.
pub trait ICS20Context: ChannelReader + ChannelKeeper + PortReader + Clone {}

