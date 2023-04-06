use crate::prelude::*;

pub const type TYPE_URL: &str = "/ibc.core.channel.v1.MsgChannelUpgradeTry";

/// Message definition for the second step of the channel upgrade 
/// handshake (the `ChanUpgradeTry` datagram).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgChannelUpgradeTry {}