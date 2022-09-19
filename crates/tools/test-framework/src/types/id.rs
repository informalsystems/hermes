/*!
   This module contains the [tagged version](crate::types::tagged) of the
   identifier types defined in [`ibc::core::ics24_host::identifier`].
*/

use crate::types::tagged::*;
use ibc::core::ics24_host::identifier::*;

/**
   A [`ChainId`] tagged with the chain it belongs to.
*/
pub type TaggedChainId<Chain> = MonoTagged<Chain, ChainId>;

/**
   A reference to [`ChainId`] tagged with the chain it
   belongs to.
*/
pub type TaggedChainIdRef<'a, Chain> = MonoTagged<Chain, &'a ChainId>;

/**
   A [`ClientId`] tagged with first, the chain it belongs to, and second,
   the counterparty chain that the client ID corresponds to.
*/
pub type TaggedClientId<ChainA, ChainB> = DualTagged<ChainA, ChainB, ClientId>;

/**
   A reference to [`ClientId`] tagged with first, the chain it belongs to,
   and second, the counterparty chain that the client ID corresponds to.
*/
pub type TaggedClientIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a ClientId>;

/**
   A [`PortId`] tagged with first, the host chain that has
   the port ID, and second, the counterparty chain that the port ID
   corresponds to.
*/
pub type TaggedPortId<ChainA, ChainB> = DualTagged<ChainA, ChainB, PortId>;

/**
   A reference to [`PortId`](PortId) tagged with first, the host chain
   that has the port ID, and second, the counterparty chain that the port ID
   corresponds to.
*/
pub type TaggedPortIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a PortId>;

/**
   A [`ChannelId`] tagged with first, the host chain that
   has the channel ID, and second, the counterparty chain that the channel
   ID corresponds to.
*/
pub type TaggedChannelId<ChainA, ChainB> = DualTagged<ChainA, ChainB, ChannelId>;

/**
   A reference to [`ChannelId`] tagged with first, the host
   chain that has the channel ID, and second, the counterparty chain that the
   channel ID corresponds to.
*/
pub type TaggedChannelIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a ChannelId>;

/**
   A [`ConnectionId`] tagged with first, the host chain
   that has the connection ID, and second, the counterparty chain that the
   connection ID corresponds to.
*/
pub type TaggedConnectionId<ChainA, ChainB> = DualTagged<ChainA, ChainB, ConnectionId>;

/**
   A reference to [`ConnectionId`] tagged with first,
   the host chain that has the connection ID, and second, the counterparty
   chain that the connection ID corresponds to.
*/
pub type TaggedConnectionIdRef<'a, ChainA, ChainB> = DualTagged<ChainA, ChainB, &'a ConnectionId>;

pub fn tagged_transfer_port<ChainA, ChainB>() -> TaggedPortId<ChainA, ChainB> {
    DualTagged::new(PortId::transfer())
}
