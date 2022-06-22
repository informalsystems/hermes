use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::timestamp::Timestamp;
use ibc::Height;

use crate::tagged::{DualTagged, MonoTagged};

#[derive(Clone, Debug)]
pub struct Packet<ChainA, ChainB> {
    pub source_port: DualTagged<ChainA, ChainB, PortId>,
    pub source_channel_id: DualTagged<ChainA, ChainB, ChannelId>,
    pub destination_port: DualTagged<ChainB, ChainA, PortId>,
    pub destination_channel_id: DualTagged<ChainB, ChainA, ChannelId>,
    pub sequence: DualTagged<ChainA, ChainB, Sequence>,
    pub timeout_height: MonoTagged<ChainB, Height>,
    pub timeout_timestamp: MonoTagged<ChainB, Timestamp>,
}
