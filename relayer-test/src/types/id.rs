use crate::tagged::*;
use ibc::core::ics24_host::identifier as base;

pub type ChainId<Chain> = MonoTagged<Chain, base::ChainId>;

pub type PortId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::PortId>;

pub type ChannelId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::ChannelId>;

pub type ConnectionId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::ConnectionId>;
