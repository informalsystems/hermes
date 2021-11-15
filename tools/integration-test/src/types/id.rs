/*!
   This module contains the [tagged version](crate::types::tagged) of the
   identifier types defined in [`ibc::core::ics24_host::identifier`].
*/

use crate::types::tagged::*;
use ibc::core::ics24_host::identifier as base;

/**
   A [`ChainId`](base::ChainId) tagged with the chain it belongs to.
*/
pub type ChainId<Chain> = MonoTagged<Chain, base::ChainId>;

/**
   A reference to [`ChainId`](base::ChainId) tagged with the chain it
   belongs to.
*/
pub type ChainIdRef<'a, Chain> = MonoTagged<Chain, &'a base::ChainId>;

/**
   A [`PortId`](base::PortId) tagged with first, the host chain that has
   the port ID, and second, the counterparty chain that the port ID
   corresponds to.
*/
pub type PortId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::PortId>;

/**
   A reference to [`PortId`](base::PortId) tagged with first, the host chain
   that has the port ID, and second, the counterparty chain that the port ID
   corresponds to.
*/
pub type PortIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a base::PortId>;

/**
   A [`ChannelId`](base::ChannelId) tagged with first, the host chain that
   has the channel ID, and second, the counterparty chain that the channel
   ID corresponds to.
*/
pub type ChannelId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::ChannelId>;

/**
   A reference to [`ChannelId`](base::ChannelId) tagged with first, the host
   chain that has the channel ID, and second, the counterparty chain that the
   channel ID corresponds to.
*/
pub type ChannelIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a base::ChannelId>;

/**
   A [`ConnectionId`](base::ConnectionId) tagged with first, the host chain
   that has the connection ID, and second, the counterparty chain that the
   connection ID corresponds to.
*/
pub type ConnectionId<ChainA, ChainB> = DualTagged<ChainA, ChainB, base::ConnectionId>;

/**
   A reference to [`ConnectionId`](base::ConnectionId) tagged with first,
   the host chain that has the connection ID, and second, the counterparty
   chain that the connection ID corresponds to.
*/
pub type ConnectionIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a base::ConnectionId>;
