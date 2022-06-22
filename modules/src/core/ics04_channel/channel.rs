use crate::prelude::*;

use crate::core::ics02_client::height::Height;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::events::WithBlockDataType;

pub use ibc_base::ics04_channel::channel::*;

/// Used to query a packet event, identified by `event_id`, for specific channel and sequences.
/// The query is preformed for the chain context at `height`.
#[derive(Clone, Debug)]
pub struct QueryPacketEventDataRequest {
    pub event_id: WithBlockDataType,
    pub source_channel_id: ChannelId,
    pub source_port_id: PortId,
    pub destination_channel_id: ChannelId,
    pub destination_port_id: PortId,
    pub sequences: Vec<Sequence>,
    pub height: Height,
}
